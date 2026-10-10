import OAI.NumberTheory.Jacobsthal.Harmonic.ComplexComponentBound

namespace OAI

namespace Erdos970

section

open UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

@[implicit_reducible]
noncomputable def complexPolynomialNormalization : StrongNormalizationMonoid (MV ℂ) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

attribute [local instance] complexPolynomialNormalization

theorem associated_constant {F G : MV ℂ} (h : Associated F G) :
    ∃ a : ℂ, a ≠ 0 ∧ G = MvPolynomial.C a * F := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨a,ha,hua⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  exact ⟨a,ha.ne_zero,by rw [← hu,hua,mul_comm]⟩

theorem associated_totalDegree {F G : MV ℂ} (h : Associated F G) : F.totalDegree = G.totalDegree := by
  obtain ⟨a,ha,rfl⟩ := associated_constant h
  exact (scalar_totalDegree a ha F).symm

theorem associated_squarePoints {F G : MV ℂ} (h : Associated F G) (S : ℝ) :
    complexSquarePoints F S = complexSquarePoints G S := by
  obtain ⟨a,ha,rfl⟩ := associated_constant h
  exact (complexSquare_scalar a ha F S).symm

theorem irreducible_totalDegree_pos {F : MV ℂ} (hF : Irreducible F) : 0 < F.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hd
  have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : F.coeff 0 ≠ 0 := by
    intro hc
    apply hF.ne_zero
    rw [he,hc,map_zero]
  apply hF.not_isUnit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

theorem totalDegree_multiset_prod (s : Multiset (MV ℂ)) (hs : ∀ F ∈ s, F ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons F s ih =>
      have hF := hs F (Multiset.mem_cons_self _ _)
      have hrest : ∀ G ∈ s, G ≠ 0 := fun G hG => hs G (Multiset.mem_cons_of_mem hG)
      have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hrest 0 h rfl)
      rw [Multiset.prod_cons,MvPolynomial.totalDegree_mul_of_isDomain hF hprod,
        Multiset.map_cons,Multiset.sum_cons,ih hrest]

theorem multiset_card_le_degree_sum (s : Multiset (MV ℂ)) (hs : ∀ F ∈ s, Irreducible F) :
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons F s ih =>
      have hF := irreducible_totalDegree_pos (hs F (Multiset.mem_cons_self _ _))
      have hrest := ih (fun G hG => hs G (Multiset.mem_cons_of_mem hG))
      simp only [Multiset.card_cons,Multiset.map_cons,Multiset.sum_cons]
      omega

theorem normalizedFactors_card_le_degree (P : MV ℂ) (hP : P ≠ 0) :
    (normalizedFactors P).card ≤ P.totalDegree := by
  have hirr := irreducible_of_normalized_factor (a := P)
  have hsum := totalDegree_multiset_prod (normalizedFactors P) (fun F hF => (hirr F hF).ne_zero)
  have hassoc := associated_totalDegree (prod_normalizedFactors hP)
  rw [hsum] at hassoc
  exact (multiset_card_le_degree_sum (normalizedFactors P) hirr).trans hassoc.le

noncomputable def nonlinearFactors (P : MV ℂ) : Finset (MV ℂ) := by
  classical
  exact (normalizedFactors P).toFinset.filter (fun F => 1 < F.totalDegree)

theorem mem_nonlinearFactors (P F : MV ℂ) :
    F ∈ nonlinearFactors P ↔ F ∈ normalizedFactors P ∧ 1 < F.totalDegree := by
  classical
  simp only [nonlinearFactors,Finset.mem_filter,Multiset.mem_toFinset]

theorem nonlinearFactors_card_le_degree (P : MV ℂ) (hP : P ≠ 0) :
    (nonlinearFactors P).card ≤ P.totalDegree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans (normalizedFactors_card_le_degree P hP))

theorem nonlinearFactor_degree_le {P F : MV ℂ} (hP : P ≠ 0) (hF : F ∈ nonlinearFactors P) :
    F.totalDegree ≤ P.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (dvd_of_mem_normalizedFactors ((mem_nonlinearFactors P F).mp hF).1) hP

end ErdosComplexCurveFactors

end

section

open Set UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization
open ErdosCriticalGeometry ErdosConvexGraph
attribute [local instance] Classical.propDecidable

def OnNonlinearComponent (P : MV ℂ) (p : ℤ × ℤ) : Prop :=
  ∃ F : MV ℂ, Irreducible F ∧ F ∣ P ∧ 1 < F.totalDegree ∧
    MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0

noncomputable def nonlinearSquarePoints (P : MV ℂ) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter (OnNonlinearComponent P)

theorem mem_nonlinearSquarePoints (P : MV ℂ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ nonlinearSquarePoints P S ↔ InSquare S p ∧ OnNonlinearComponent P p := by
  simp only [nonlinearSquarePoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem nonlinearSquare_eq_union (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) :
    nonlinearSquarePoints P S = (nonlinearFactors P).biUnion (fun F => complexSquarePoints F S) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hs,F,hF,hdiv,hdeg,hzero⟩ := (mem_nonlinearSquarePoints P S p).mp hp
    obtain ⟨G,hG,hFG⟩ := exists_mem_normalizedFactors_of_dvd hP hF hdiv
    have hGdeg : 1 < G.totalDegree := by rwa [← associated_totalDegree hFG]
    have hpG : p ∈ complexSquarePoints G S := by
      rw [← associated_squarePoints hFG S]
      exact (mem_complexSquarePoints F S p).mpr ⟨hs,hzero⟩
    exact Finset.mem_biUnion.mpr ⟨G,(mem_nonlinearFactors P G).mpr ⟨hG,hGdeg⟩,hpG⟩
  · intro hp
    obtain ⟨F,hF,hpF⟩ := Finset.mem_biUnion.mp hp
    have hnorm := (mem_nonlinearFactors P F).mp hF
    have hpoint := (mem_complexSquarePoints F S p).mp hpF
    exact (mem_nonlinearSquarePoints P S p).mpr
      ⟨hpoint.1,F,irreducible_of_normalized_factor F hnorm.1,
        dvd_of_mem_normalizedFactors hnorm.1,hnorm.2,hpoint.2⟩

end ErdosComplexCurveFactors

end

section

open Set UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization
open ErdosCriticalGeometry

theorem nonlinear_square_degree_four_bound (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) (hS : 0 ≤ S) :
    ((nonlinearSquarePoints P S).card : ℝ) ≤
      182*(P.totalDegree : ℝ)^4*(1+S^((2 : ℝ)/3)) := by
  classical
  have hbound (F : MV ℂ) (hF : F ∈ nonlinearFactors P) :
      ((complexSquarePoints F S).card : ℝ) ≤
        182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
    have hm := (mem_nonlinearFactors P F).mp hF
    calc
      _ ≤ 182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) :=
        irreducible_complex_curve_bound F (irreducible_of_normalized_factor F hm.1) hm.2 S hS
      _ ≤ _ := by
        gcongr
        exact_mod_cast nonlinearFactor_degree_le hP hF
  have hc : (nonlinearSquarePoints P S).card ≤
      ∑ F ∈ nonlinearFactors P, (complexSquarePoints F S).card := by
    rw [nonlinearSquare_eq_union P hP S]
    exact Finset.card_biUnion_le
  calc
    ((nonlinearSquarePoints P S).card : ℝ) ≤
        ∑ F ∈ nonlinearFactors P, ((complexSquarePoints F S).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _F ∈ nonlinearFactors P, 182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) :=
      Finset.sum_le_sum hbound
    _ = ((nonlinearFactors P).card : ℝ)*(182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3))) := by simp
    _ ≤ (P.totalDegree : ℝ)*(182*(P.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast nonlinearFactors_card_le_degree P hP) (by positivity)
    _ = 182*(P.totalDegree : ℝ)^4*(1+S^((2 : ℝ)/3)) := by ring

theorem nonlinear_square_bound_of_degree_le (P : MV ℂ) (hP : P ≠ 0) (D : ℕ)
    (hD : P.totalDegree ≤ D) (S : ℝ) (hS : 0 ≤ S) :
    ((nonlinearSquarePoints P S).card : ℝ) ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) := by
  apply (nonlinear_square_degree_four_bound P hP S hS).trans
  gcongr

end ErdosComplexCurveFactors

end

section

open Set
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosConvexGraph

noncomputable def realNonlinearSquarePoints (P : MV ℝ) (S : ℝ) : Finset (ℤ × ℤ) :=
  nonlinearSquarePoints (complexify P) S

theorem mem_realNonlinearSquarePoints (P : MV ℝ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ realNonlinearSquarePoints P S ↔ InSquare S p ∧
      ∃ F : MV ℂ, Irreducible F ∧ F ∣ MvPolynomial.map (algebraMap ℝ ℂ) P ∧
        1 < F.totalDegree ∧ MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 := by
  simp only [realNonlinearSquarePoints,mem_nonlinearSquarePoints,OnNonlinearComponent,complexify]

theorem complexify_ne_zero {P : MV ℝ} (hP : P ≠ 0) : complexify P ≠ 0 := by
  intro h
  apply hP
  apply MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  simpa only [complexify,map_zero] using h

theorem degree_uniform_nonlinear_lattice_bound (P : MV ℝ) (hP : P ≠ 0) (D : ℕ)
    (hD : P.totalDegree ≤ D) (S : ℝ) (hS : 0 ≤ S) :
    ((realNonlinearSquarePoints P S).card : ℝ) ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) :=
  nonlinear_square_bound_of_degree_le (complexify P) (complexify_ne_zero hP) D
    (by rwa [complexify_totalDegree]) S hS

theorem exists_absolute_nonlinear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ P : MV ℝ, P ≠ 0 → ∀ D : ℕ, 1 ≤ D → P.totalDegree ≤ D →
      ∀ S : ℝ, 1 ≤ S → ((realNonlinearSquarePoints P S).card : ℝ) ≤
        C*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) := by
  refine ⟨182,by norm_num,?_⟩
  intro P hP D _ hD S hS
  exact degree_uniform_nonlinear_lattice_bound P hP D hD S (le_trans zero_le_one hS)

end ErdosComplexCurveFactors

end

section

open UniqueFactorizationMonoid
namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph
attribute [local instance] complexPolynomialNormalization

noncomputable def linearFactors (P : MV ℂ) : Finset (MV ℂ) := by
  classical
  exact (normalizedFactors P).toFinset.filter (fun F => F.totalDegree = 1)

theorem mem_linearFactors (P F : MV ℂ) :
    F ∈ linearFactors P ↔ F ∈ normalizedFactors P ∧ F.totalDegree = 1 := by
  classical
  simp only [linearFactors,Finset.mem_filter,Multiset.mem_toFinset]

theorem linearFactors_card_le_degree (P : MV ℂ) (hP : P ≠ 0) :
    (linearFactors P).card ≤ P.totalDegree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans (normalizedFactors_card_le_degree P hP))

theorem zero_mem_normalized_factor (P : MV ℂ) (hP : P ≠ 0) (p : ℤ × ℤ)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] P = 0) :
    ∃ F ∈ normalizedFactors P, MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 := by
  classical
  let ev := MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)]
  obtain ⟨a,ha,hprod⟩ := associated_constant (prod_normalizedFactors hP)
  have hz : ev (normalizedFactors P).prod = 0 := by
    have h := hp
    rw [hprod,map_mul,MvPolynomial.eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left ha
  rw [map_multiset_prod] at hz
  obtain ⟨F,hF,hzF⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
  exact ⟨F,hF,hzF⟩

theorem square_zero_cover (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) :
    complexSquarePoints P S ⊆ nonlinearSquarePoints P S ∪
      (linearFactors P).biUnion (fun F => complexSquarePoints F S) := by
  classical
  intro p hp
  obtain ⟨hs,hzero⟩ := (mem_complexSquarePoints P S p).mp hp
  obtain ⟨F,hF,hzF⟩ := zero_mem_normalized_factor P hP p hzero
  have hirr := irreducible_of_normalized_factor F hF
  have hpos := irreducible_totalDegree_pos hirr
  by_cases hdeg : F.totalDegree = 1
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨F,(mem_linearFactors P F).mpr ⟨hF,hdeg⟩,
        (mem_complexSquarePoints F S p).mpr ⟨hs,hzF⟩⟩)
  · exact Finset.mem_union_left _ ((mem_nonlinearSquarePoints P S p).mpr
      ⟨hs,F,hirr,dvd_of_mem_normalizedFactors hF,by omega,hzF⟩)

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization

theorem selected_point_cover (P : MV ℂ) (hP : P ≠ 0) (S : ℝ) (X : Finset (ℤ × ℤ))
    (hX : X ⊆ complexSquarePoints P S) :
    X ⊆ nonlinearSquarePoints P S ∪
      (linearFactors P).biUnion (fun F => X ∩ complexSquarePoints F S) := by
  classical
  intro p hp
  rcases Finset.mem_union.mp (square_zero_cover P hP S (hX hp)) with hn | hl
  · exact Finset.mem_union_left _ hn
  · obtain ⟨F,hF,hpF⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F,hF,Finset.mem_inter.mpr ⟨hp,hpF⟩⟩)

theorem selected_count_bound (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (M : ℝ) (hM : 0 ≤ M)
    (hsmall : ∀ F ∈ linearFactors P, ((X ∩ complexSquarePoints F S).card : ℝ) ≤ M) :
    (X.card : ℝ) ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M := by
  classical
  have hc : X.card ≤ (nonlinearSquarePoints P S).card+
      ∑ F ∈ linearFactors P, (X ∩ complexSquarePoints F S).card :=
    (Finset.card_le_card (selected_point_cover P hP S X hX)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hlines : ((linearFactors P).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (linearFactors_card_le_degree P hP).trans hD
  calc
    (X.card : ℝ) ≤ ((nonlinearSquarePoints P S).card : ℝ)+
        ∑ F ∈ linearFactors P, ((X ∩ complexSquarePoints F S).card : ℝ) := by exact_mod_cast hc
    _ ≤ 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+∑ _F ∈ linearFactors P, M :=
      add_le_add (nonlinear_square_bound_of_degree_le P hP D hD S hS) (Finset.sum_le_sum hsmall)
    _ = 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+((linearFactors P).card : ℝ)*M := by simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hlines hM)

theorem exists_rich_linear_factor (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (M : ℝ) (hM : 0 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ F : MV ℂ, Irreducible F ∧ F ∣ P ∧ F.totalDegree = 1 ∧
      M < ((X ∩ complexSquarePoints F S).card : ℝ) := by
  classical
  have hex : ∃ F ∈ linearFactors P, M < ((X ∩ complexSquarePoints F S).card : ℝ) := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hlarge) (selected_count_bound P hP D hD S hS X hX M hM h)
  obtain ⟨F,hF,hcard⟩ := hex
  have hn := (mem_linearFactors P F).mp hF
  exact ⟨F,UniqueFactorizationMonoid.irreducible_of_normalized_factor F hn.1,
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hn.1,hn.2,hcard⟩

end ErdosRichLine

end

end Erdos970

end OAI
