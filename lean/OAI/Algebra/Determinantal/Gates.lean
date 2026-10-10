import OAI.Algebra.Determinantal.Selector

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

noncomputable def blockExponent (d : I → J →₀ ℕ) : I × J →₀ ℕ :=
  ∑ i, (d i).mapDomain (fun j => (i,j))

omit [Fintype I] in
 theorem mapDomain_block_apply (d : J →₀ ℕ) (i k : I) (j : J) :
    d.mapDomain (fun j => (i,j)) (k,j) = if i = k then d j else 0 := by
  classical
  by_cases h : i = k
  · subst k
    simpa using Finsupp.mapDomain_apply_of_injective (fun a b h => congrArg Prod.snd h) d j
  · rw [ite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact h (congrArg Prod.fst ha)

 @[simp] theorem blockExponent_apply (d : I → J →₀ ℕ) (i : I) (j : J) :
    blockExponent d (i,j) = d i j := by
  classical
  simp only [blockExponent, Finsupp.finsetSum_apply, mapDomain_block_apply]
  simp

 theorem blockExponent_injective : Function.Injective (blockExponent (I := I) (J := J)) := by
  intro d e h
  funext i
  ext j
  simpa using congrArg (fun a : I × J →₀ ℕ => a (i,j)) h

 theorem coeff_independent_blocks (p : I → MvPolynomial J R) (d : I → J →₀ ℕ) :
    (∏ i, rename (fun j => (i,j)) (p i)).coeff (blockExponent d) =
      ∏ i, (p i).coeff (d i) := by
  classical
  have hexp (i : I) : rename (fun j => (i,j)) (p i) =
      ∑ k ∈ (p i).support, monomial (k.mapDomain (fun j => (i,j))) ((p i).coeff k) := by
    conv_lhs => rw [MvPolynomial.as_sum (p i)]
    simp only [map_sum, rename_monomial]
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [← monomial_sum_prod, coeff_monomial]
  change (∑ k ∈ Fintype.piFinset (fun i => (p i).support),
    if blockExponent k = blockExponent d then ∏ i, (p i).coeff (k i) else 0) = _
  simp only [blockExponent_injective.eq_iff]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k _ h; simp [h]
  · intro hd
    have hnot : ¬ ∀ i, d i ∈ (p i).support := by
      simpa only [Fintype.mem_piFinset] using hd
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    simp only [mem_support_iff, not_not] at hi
    simp only [ite_true]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

 theorem eliminate_gadget_network (outside : R) (w a b c d : I → R) :
    (C outside * ∏ i, rename (fun j => (i,j))
      (gadgetEdges (-2*w i*a i) (b i) (c i) (d i))).coeff
        (blockExponent (fun (_ : I) => threeOnes.sumElim threeOnes)) =
      outside * (-2 : R) ^ Fintype.card I * ∏ i, (1 + w i*a i*b i*c i*d i) := by
  rw [coeff_C_mul, coeff_independent_blocks]
  simp_rw [gadgetEdges_coefficient]
  have h (i : I) : (-2 + (-2*w i*a i)*b i*c i*d i) =
      (-2:R) * (1 + w i*a i*b i*c i*d i) := by ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_assoc]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I G E R : Type*} [Fintype E] [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] [CommRing R]

abbrev ExpandedVertex (I G : Type*) := I ⊕ (G × Fin 3)
abbrev InternalVertex (G : Type*) := G × (Fin 3 ⊕ Fin 3)
abbrev GadgetLabels := Fin 2 ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))
abbrev ExpandedLabels (E G : Type*) := E ⊕ (G × GadgetLabels)

noncomputable def baseEdges (src dst : E → I) (ω : E → R) : MvPolynomial (I ⊕ I) R :=
  ∏ e, (1 + monomial (edgeExponent (src e,dst e)) (ω e))

def vertexSplit : (ExpandedVertex I G ⊕ ExpandedVertex I G) ≃
    (InternalVertex G ⊕ (I ⊕ I)) where
  toFun
  | .inl (.inl i) => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr i)
  | .inl (.inr (g,r)) => .inl (g,.inl r)
  | .inr (.inr (g,c)) => .inl (g,.inr c)
  invFun
  | .inr (.inl i) => .inl (.inl i)
  | .inr (.inr i) => .inr (.inl i)
  | .inl (g,.inl r) => .inl (.inr (g,r))
  | .inl (g,.inr c) => .inr (.inr (g,c))
  left_inv x := by rcases x with (i|⟨g,r⟩)|(i|⟨g,c⟩) <;> rfl
  right_inv x := by rcases x with ⟨g,r|c⟩|(i|j) <;> rfl

 theorem allOnes_map_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    (allOnes A).mapDomain e = allOnes B := by
  classical
  ext b
  obtain ⟨a,rfl⟩ := e.surjective b
  rw [Finsupp.mapDomain_apply_of_injective e.injective]
  rfl

noncomputable def expandedSrc (src : E → I) (u₁ u₂ : G → I) : ExpandedLabels E G → ExpandedVertex I G
  | .inl e => .inl (src e)
  | .inr (g,.inl b) => .inl (if b=0 then u₁ g else u₂ g)
  | .inr (g,.inr (.inl r)) => .inr (g,r)
  | .inr (g,.inr (.inr (r,_))) => .inr (g,r)
noncomputable def expandedDst (dst : E → I) (v₁ v₂ : G → I) : ExpandedLabels E G → ExpandedVertex I G
  | .inl e => .inl (dst e)
  | .inr (g,.inl b) => .inr (g,b.castLE (by decide))
  | .inr (g,.inr (.inl r)) => .inl (if r=0 then v₁ g else v₂ g)
  | .inr (g,.inr (.inr (_,c))) => .inr (g,c)
noncomputable def expandedWeight (ω : E → R) (w : G → R) : ExpandedLabels E G → R
  | .inl e => ω e
  | .inr (g,.inl b) => if b=0 then -2*w g else 1
  | .inr (_,.inr (.inl r)) => if r=2 then 0 else 1
  | .inr (_,.inr (.inr (r,c))) => gadgetH r c

noncomputable def expandedMatrix (src dst : E → I) (ω : E → R) (w : G → R)
    (u₁ u₂ v₁ v₂ : G → I) : Matrix (ExpandedVertex I G) (ExpandedVertex I G) R :=
  graphMatrix (expandedSrc src u₁ u₂) (expandedDst dst v₁ v₂) (expandedWeight ω w)

noncomputable def splitPolynomial : MvPolynomial (ExpandedVertex I G ⊕ ExpandedVertex I G) R →+*
    MvPolynomial (InternalVertex G) (MvPolynomial (I ⊕ I) R) :=
  (sumRingEquiv R _ _).toRingHom.comp ((rename vertexSplit).toRingHom)

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_C (a : R) :
    splitPolynomial (I := I) (G := G) (C a) = C (C a) := by
  simp [splitPolynomial]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_outer_left (i : I) :
    splitPolynomial (G := G) (X (.inl (.inl i)) : MvPolynomial _ R) = C (X (.inl i)) := by
  simp [splitPolynomial, vertexSplit]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_outer_right (i : I) :
    splitPolynomial (G := G) (X (.inr (.inl i)) : MvPolynomial _ R) = C (X (.inr i)) := by
  simp [splitPolynomial, vertexSplit]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_inner_left (g : G) (r : Fin 3) :
    splitPolynomial (I := I) (X (.inl (.inr (g,r))) : MvPolynomial _ R) = X (g,.inl r) := by
  simp [splitPolynomial, vertexSplit]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_inner_right (g : G) (c : Fin 3) :
    splitPolynomial (I := I) (X (.inr (.inr (g,c))) : MvPolynomial _ R) = X (g,.inr c) := by
  simp [splitPolynomial, vertexSplit]

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 theorem split_edge (i j : ExpandedVertex I G) (a : R) :
    splitPolynomial (1 + monomial (edgeExponent (i,j)) a) =
    1 + splitPolynomial (C a) * splitPolynomial (X (.inl i)) * splitPolynomial (X (.inr j)) := by
  have hm : monomial (edgeExponent (i,j)) a = C a * X (.inl i) * X (.inr j) := by
    rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
    simp only [edgeExponent,mul_one]
  rw [hm, map_add, map_one, map_mul, map_mul]

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 theorem gadget_factors (g : G) (w : R) (a b c d : I) :
    (∏ x : Fin 2,
        (1 + C (C (if x = 0 then -2 * w else 1)) * C (X (Sum.inl (if x = 0 then a else b))) *
            X (g, Sum.inr (x.castLE (by decide))))) *
      ((∏ x : Fin 3, (1 + C (C (if x = 2 then 0 else 1)) * X (g, Sum.inl x) *
          C (X (Sum.inr (if x = 0 then c else d))))) *
        ∏ x : Fin 3, ∏ y : Fin 3, (1 + C (C (gadgetH x y : R)) * X (g, Sum.inl x) * X (g, Sum.inr y))) =
    rename (fun z => (g,z))
      (gadgetEdges (-2*C w*X (.inl a)) (X (.inl b)) (X (.inr c)) (X (.inr d))) := by
  classical
  simp only [gadgetEdges, map_mul, map_prod, map_add, map_one, rename_C, rename_X]
  rw [Finset.prod_mul_distrib]
  apply congrArg₂ (·*·)
  · simp [Fin.prod_univ_succ, map_mul, mul_assoc, map_ofNat, neg_mul]
    ring
  · apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro i _
      fin_cases i <;> simp [mul_comm]
    · apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      have hc : C (gadgetH i j : R) = (gadgetH i j : MvPolynomial (I ⊕ I) R) := by
        fin_cases i <;> fin_cases j <;> simp [gadgetH]
      rw [hc]
      ac_rfl

omit [Fintype I] [DecidableEq I] [DecidableEq G] in
 theorem split_expanded_edges (src dst : E → I) (ω : E → R) (w : G → R) (u₁ u₂ v₁ v₂ : G → I) :
    splitPolynomial (∏ e, (1 + monomial
      (edgeExponent (expandedSrc src u₁ u₂ e, expandedDst dst v₁ v₂ e)) (expandedWeight ω w e))) =
    C (baseEdges src dst ω) * ∏ g, rename (fun z => (g,z))
      (gadgetEdges (-2*C (w g)*X (.inl (u₁ g))) (X (.inl (u₂ g)))
        (X (.inr (v₁ g))) (X (.inr (v₂ g)))) := by
  classical
  simp only [map_prod, map_mul, Fintype.prod_sum_type, Fintype.prod_prod_type,
    split_edge, expandedSrc, expandedDst, expandedWeight, splitPolynomial_C,
    splitPolynomial_outer_left, splitPolynomial_outer_right,
    splitPolynomial_inner_left, splitPolynomial_inner_right]
  congr 1
  · simp only [baseEdges, map_prod, map_add, map_one]
    apply Finset.prod_congr rfl
    intro e _
    have hm : monomial (edgeExponent (src e,dst e)) (ω e) =
        C (ω e)*X (.inl (src e))*X (.inr (dst e)) := by
      rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
      simp only [edgeExponent, mul_one]
    rw [hm, map_mul, map_mul]
  · apply Finset.prod_congr rfl
    intro g _
    exact gadget_factors g (w g) (u₁ g) (u₂ g) (v₁ g) (v₂ g)

 theorem block_three_ones : blockExponent (fun (_ : G) => threeOnes.sumElim threeOnes) =
    allOnes (InternalVertex G) := by
  classical
  ext ⟨g,i⟩
  simp only [blockExponent, Finsupp.finsetSum_apply, mapDomain_block_apply]
  rw [Finset.sum_eq_single g]
  · simp only
    cases i with
    | inl i => fin_cases i <;> simp [threeOnes, allOnes]
    | inr i => fin_cases i <;> simp [threeOnes, allOnes]
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq I] [DecidableEq G] in
 theorem splitPolynomial_top_coefficient
    (p : MvPolynomial (ExpandedVertex I G ⊕ ExpandedVertex I G) R) :
    p.coeff (allOnes _) = ((splitPolynomial p).coeff (allOnes (InternalVertex G))).coeff
      (allOnes (I ⊕ I)) := by
  have h := coeff_rename_mapDomain vertexSplit vertexSplit.injective p (allOnes _)
  rw [allOnes_map_equiv] at h
  rw [← h]
  have ho : allOnes (InternalVertex G ⊕ (I ⊕ I)) =
      (allOnes (InternalVertex G)).sumElim (allOnes (I ⊕ I)) := by
    ext x; cases x <;> rfl
  rw [ho, coeff_nested]
  rfl

 theorem expanded_permanent (src dst : E → I) (ω : E → R) (w : G → R) (u₁ u₂ v₁ v₂ : G → I) :
    (expandedMatrix src dst ω w u₁ u₂ v₁ v₂).permanent =
      (-2:R)^Fintype.card G * (baseEdges src dst ω * ∏ g,
      (1 + C (w g)*X (.inl (u₁ g))*X (.inl (u₂ g))*
        X (.inr (v₁ g))*X (.inr (v₂ g)))).coeff (allOnes (I ⊕ I)) := by
  rw [expandedMatrix, ← coeff_graph_edges, splitPolynomial_top_coefficient,
    split_expanded_edges, ← block_three_ones]
  rw [eliminate_gadget_network]
  have hc : (-2 : MvPolynomial (I ⊕ I) R)^Fintype.card G = C ((-2:R)^Fintype.card G) := by simp only [map_pow, map_neg, map_ofNat]
  rw [hc, mul_comm (baseEdges src dst ω), mul_assoc, coeff_C_mul]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem colored_diagonal_edges (M : Matrix I I R) (s t : I → R) :
    (edgeProduct M * (∏ i, (1 + C (s i)*X (.inl i)*X (.inr i))) *
      (∏ i, (1 + C (t i)*X (.inl i)*X (.inr i)))).coeff (allOnes (I ⊕ I)) =
      (M + Matrix.diagonal (fun i => s i+t i)).permanent := by
  classical
  let src : (I × I) ⊕ (I ⊕ I) → I
    | .inl (i,_) => i
    | .inr (.inl i) => i
    | .inr (.inr i) => i
  let dst : (I × I) ⊕ (I ⊕ I) → I
    | .inl (_,j) => j
    | .inr (.inl i) => i
    | .inr (.inr i) => i
  let w : (I × I) ⊕ (I ⊕ I) → R
    | .inl (i,j) => M i j
    | .inr (.inl i) => s i
    | .inr (.inr i) => t i
  have hm (i : I) (r : R) : monomial (edgeExponent (i,i)) r =
      C r*X (.inl i)*X (.inr i) := by
    rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
    simp only [edgeExponent,mul_one]
  have hpoly : (∏ e, (1 + monomial (edgeExponent (src e,dst e)) (w e))) =
      edgeProduct M * (∏ i, (1 + C (s i)*X (.inl i)*X (.inr i))) *
      (∏ i, (1 + C (t i)*X (.inl i)*X (.inr i))) := by
    simp only [Fintype.prod_sum_type, src,dst,w,hm,edgeProduct,mul_assoc]
  rw [← hpoly, coeff_graph_edges]
  congr 1
  ext i j
  simp only [graphMatrix, Fintype.sum_sum_type, Fintype.sum_prod_type, src,dst,w,
    Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hij : i=j
  · subst j
    simp [and_self, ite_and]
  · simp [hij, ite_and]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem coeff_commAlgEquiv (p : MvPolynomial A (MvPolynomial B R))
    (d : A →₀ ℕ) (e : B →₀ ℕ) :
    ((commAlgEquiv R A B p).coeff e).coeff d = (p.coeff d).coeff e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp,hq]
  | monomial f r =>
    induction r using MvPolynomial.induction_on' with
    | add r s hr hs => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hr,hs]
    | monomial g x =>
      have h : commAlgEquiv R A B (monomial f (monomial g x)) =
          monomial g (monomial f x) := by
        exact AddMonoidAlgebra.commAlgEquiv_single_single ..
      rw [h]
      by_cases hf : f=d <;> by_cases hg : g=e <;> simp [coeff_monomial, hf,hg]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R S : Type*} [CommSemiring R] [CommSemiring S]
 theorem commAlgEquiv_map_C (p : MvPolynomial A R) :
    commAlgEquiv R A B (map C p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp,hq]
  | mul_X p i hp => simp [hp]

 theorem edgeProduct_map {I : Type*} [Fintype I] (M : Matrix I I R) (f : R →+* S) :
    edgeProduct (Matrix.of fun i j => f (M i j)) = map f (edgeProduct M) := by
  simp [edgeProduct, map_prod, Matrix.of_apply]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def countIndex (q : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => q)
noncomputable def elementaryBoundary (a : I → R) (q : ℕ) : R :=
  (∏ i, (1 + Polynomial.C (a i)*Polynomial.X)).coeff q
noncomputable def diagonalCoefficient (M : Matrix I I R) (θ : I → R) (q : ℕ) : R :=
  ((Matrix.of fun i j => C (M i j) : Matrix I I (MvPolynomial (Fin 2) R)) +
    (Matrix.diagonal (fun i => X (0 : Fin 2) + C (θ i)*X 1) : Matrix I I (MvPolynomial (Fin 2) R))).permanent.coeff
    (countIndex q)

omit [DecidableEq I] in
 theorem swap_colored_edge_product (M : Matrix I I R) (θ : I → R) :
    commAlgEquiv R (I ⊕ I) (Fin 2)
      (edgeProduct (Matrix.of fun i j => C (M i j)) *
        (∏ i, (1 + C (X 0)*X (.inl i)*X (.inr i))) *
        (∏ i, (1 + C (C (θ i)*X 1)*X (.inl i)*X (.inr i)))) =
    C (edgeProduct M) * (∏ i, (1 + C (X (.inl i)*X (.inr i))*X 0)) *
      (∏ i, (1 + C (C (θ i)*X (.inl i)*X (.inr i))*X 1)) := by
  rw [edgeProduct_map, map_mul, map_mul, commAlgEquiv_map_C]
  simp only [map_prod]
  apply congrArg₂ (·*·)
  · apply congrArg (C (edgeProduct M) * ·)
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_add, map_one, map_mul, commAlgEquiv_C_X, commAlgEquiv_X]
    ring
  · apply Finset.prod_congr rfl
    intro i _
    simp only [map_add, map_one, map_mul, commAlgEquiv_C, map_mul, map_C,
      map_X, commAlgEquiv_X]
    ring

omit [DecidableEq I] in
 theorem two_color_coefficient (e : R) (a b : I → R) (q : ℕ) :
    (C e * (∏ i, (1 + C (a i)*X 0)) * (∏ i, (1 + C (b i)*X 1)) :
      MvPolynomial (Fin 2) R).coeff (countIndex q) =
    e * elementaryBoundary a q * elementaryBoundary b q := by
  let p : Fin 2 → Polynomial R :=
    ![∏ i, (1 + Polynomial.C (a i)*Polynomial.X),
      ∏ i, (1 + Polynomial.C (b i)*Polynomial.X)]
  have h : (∏ x, Polynomial.eval₂ C (X x) (p x)) =
      (∏ i, (1 + C (a i)*X (0:Fin 2))) * (∏ i, (1 + C (b i)*X 1)) := by
    simp [p, Fin.prod_univ_succ, Polynomial.eval₂_finsetProd]
  rw [mul_assoc, ← h, coeff_C_mul, coeff_separate_univariate]
  simp [p, Fin.prod_univ_succ, elementaryBoundary, countIndex, mul_assoc]

 theorem diagonalCoefficient_boundary (M : Matrix I I R) (θ : I → R) (q : ℕ) :
    diagonalCoefficient M θ q =
    (edgeProduct M * elementaryBoundary (fun i => X (.inl i)*X (.inr i)) q *
      elementaryBoundary (fun i => C (θ i)*X (.inl i)*X (.inr i)) q).coeff (allOnes (I ⊕ I)) := by
  have h := colored_diagonal_edges (Matrix.of fun i j => C (M i j) : Matrix I I (MvPolynomial (Fin 2) R))
    (fun _ => X 0) (fun i => C (θ i)*X 1)
  apply_fun (fun p : MvPolynomial (Fin 2) R => p.coeff (countIndex q)) at h
  rw [← coeff_commAlgEquiv, swap_colored_edge_product, two_color_coefficient] at h
  simpa only [diagonalCoefficient] using h.symm
end PermanentBorder.Selector

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

noncomputable def subsetExponent (s : Finset I) : I →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

omit [Fintype I] in
@[simp] theorem subsetExponent_apply (s : Finset I) (i : I) :
    subsetExponent s i = if i ∈ s then 1 else 0 := by
  classical
  by_cases h : i ∈ s <;> simp [subsetExponent, h]

omit [Fintype I] in
@[simp] theorem subsetExponent_support (s : Finset I) : (subsetExponent s).support = s := by
  ext i; simp [Finsupp.mem_support_iff]

omit [Fintype I] in
@[simp] theorem subsetExponent_degree (s : Finset I) :
    (subsetExponent s).sum (fun _ m => m) = s.card := by
  simp [Finsupp.sum, subsetExponent_apply]

omit [Fintype I] in
@[simp] theorem subsetExponent_multinomial (s : Finset I) :
    (subsetExponent s).multinomial = s.card.factorial := by
  simp only [Finsupp.multinomial, Finsupp.sum, Finsupp.prod, subsetExponent_support,
    subsetExponent_apply]
  have hsum : (∑ x ∈ s, (if x ∈ s then 1 else 0)) = s.card := by simp
  have hprod : (∏ x ∈ s, (if x ∈ s then 1 else 0).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    rw [ite_eq_left hx]; rfl
  simp only [id_eq, hsum, hprod, Nat.div_one]

 theorem coeff_gate_half (s : Finset I) (h : ℕ) :
    ((∑ i, X i : MvPolynomial I R)^h).coeff (subsetExponent s) =
      if s.card = h then (h.factorial : R) else 0 := by
  rw [coeff_sum_X_pow_of_fintype, subsetExponent_degree, subsetExponent_multinomial]
  split_ifs with hs
  · rw [hs]
  · simp
end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem sumRingEquiv_monomial (d : A →₀ ℕ) (e : B →₀ ℕ) (r : R) :
    sumRingEquiv R A B (monomial (d.sumElim e) r) = monomial d (monomial e r) := by
  simp [sumRingEquiv, monomial]
 theorem coeff_nested (p : MvPolynomial (A ⊕ B) R) (d : A →₀ ℕ) (e : B →₀ ℕ) :
    p.coeff (d.sumElim e) = ((sumRingEquiv R A B p).coeff d).coeff e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, hp, hq]
  | monomial f r =>
    obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppAddEquivProdFinsupp.symm.surjective f
    have hab : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) = a.sumElim b := by
      ext x; cases x <;> rfl
    rw [hab, sumRingEquiv_monomial]
    simp only [coeff_monomial]
    have habde : a.sumElim b = d.sumElim e ↔ a = d ∧ b = e := by
      constructor
      · intro h; constructor
        · ext x; exact congrArg (fun f => f (Sum.inl x)) h
        · ext x; exact congrArg (fun f => f (Sum.inr x)) h
      · rintro ⟨rfl, rfl⟩; rfl
    simp only [habde]
    by_cases ha : a = d <;> by_cases hb : b = e <;> simp [ha, hb]
end PermanentBorder.Selector.Gates

end OAI
