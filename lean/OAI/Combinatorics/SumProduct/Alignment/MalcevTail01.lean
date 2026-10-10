import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped commutatorElement BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace MalcevHorizontal
open CubeFaces LeibmanSquare RationalLattice _root_.Polynomial _root_.OAI.Polynomial
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤)
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)

include hlevel in
lemma character_lower_trivial (k : Fin d → ℤ) (u : H.level 2) : character c hd hlin k u=1 := by
  change Multiplicative.ofAdd (∑ i,(k i:ℝ)*horizontal c hd u i)=1
  rw [(hlevel u).mp u.property]
  simp

include h0 hlevel in
lemma original_horizontal_linear {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1)
    (k : Fin d → ℤ) (z : ℤ) :
    (character c hd hlin k (f z)).toAdd=(z:ℝ)*∑ i,(k i:ℝ)*horizontal c hd (f 1) i := by
  have he := congrArg (character c hd hlin k) (linearRemainder_mul H h0 hf hf0 z)
  rw [map_mul,character_lower_trivial c hd hlin H hlevel,map_zpow,one_mul] at he
  have hh:=congrArg Multiplicative.toAdd he
  simpa only [toAdd_zpow,zsmul_eq_mul,character,MonoidHom.coe_mk,OneHom.coe_mk,toAdd_ofAdd] using hh

include h0 hlevel in
 

theorem original_horizontal_obstruction
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1)
    (R N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (k : Fin d → ℤ) (hk : k≠0) (hkR : ∀ i, |k i| ≤ R)
    (m : ℤ) (hm : |(∑ i,(k i:ℝ)*horizontal c hd (f 1) i)-m| ≤ A/N) :
    ∃ χ : G →* Multiplicative ℝ, χ≠1 ∧ Continuous χ ∧
      (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z) ∧
      (∃ k' : Fin d → ℤ, (∀ i, |k' i| ≤ R) ∧ χ=character c hd hlin k') ∧
      ∃ P : ℝ[X], P.natDegree ≤ 1 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
        ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  let α:=∑ i,(k i:ℝ)*horizontal c hd (f 1) i
  refine ⟨character c hd hlin k,character_ne_one c hd hlin hk,character_continuous c hd hlin k,
    fun g hg => character_integer c hd hlin Γ hΓ k hg,⟨k,hkR,rfl⟩,C α*X,?_,?_,?_⟩
  · exact (natDegree_mul_le.trans (by simp [natDegree_C,natDegree_X]))
  · intro z
    rw [eval_mul,eval_C,eval_X,original_horizontal_linear c hd hlin H h0 hlevel hf hf0 k z]
    change α*(z:ℝ)=(z:ℝ)*α
    ring
  · intro j hj
    by_cases hj1 : j=1
    · subst j
      exact ⟨m,by simpa [coeff_C_mul,α] using hm⟩
    · refine ⟨0,?_⟩
      simp only [coeff_C_mul,coeff_X,ite_eq_right (Ne.symm hj1),mul_zero,Int.cast_zero,sub_zero,abs_zero]
      positivity

end MalcevHorizontal
end
end
 

 
section
noncomputable section
namespace MalcevHorizontal
open RationalLattice CubeFaces LeibmanSquare BracketHyperplanes
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)

include hlin in
lemma horizontal_pow (a : G) (h : ℕ) :
    horizontal c hd (a^h)=fun i => (h:ℝ)*horizontal c hd a i := by
  have he := congrArg Multiplicative.toAdd (map_pow (quotientHom c hd hlin) a h)
  rw [toAdd_pow] at he
  change horizontal c hd (a^h)=h • horizontal c hd a at he
  funext i
  simpa only [Pi.smul_apply,nsmul_eq_mul] using congrFun he i

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hlin hΓ in
 

lemma representative_torus (a : G) (v : ℕ → G)
    (hv : ∀ h, (v h)⁻¹*a^h∈Γ) (h : ℕ) :
    BracketHyperplanes.torusMap (horizontal c hd (v h))=
      BracketHyperplanes.torusMap (fun i => horizontal c hd a i*(h:ℝ)+(0:Fin d → ℝ) i) := by
  funext i
  obtain ⟨z,hz⟩ := (hΓ ((v h)⁻¹*a^h)).mp (hv h) (Fin.castLE hd i)
  change horizontal c hd ((v h)⁻¹*a^h) i=(z:ℝ) at hz
  rw [horizontal_mul c hd hlin,horizontal_inv c hd hlin,horizontal_pow c hd hlin] at hz
  change -horizontal c hd (v h) i+(h:ℝ)*horizontal c hd a i=(z:ℝ) at hz
  have he : horizontal c hd a i*(h:ℝ)=horizontal c hd (v h) i+(z:ℝ) := by linarith
  change (horizontal c hd (v h) i:UnitAddCircle)=
    ((horizontal c hd a i*(h:ℝ)+0:ℝ):UnitAddCircle)
  rw [he]
  simp

lemma reduced_horizontal_bound (a : G) : ‖horizontal c hd (reduceCoordinates c a n)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  have hi := reduceCoordinates_bounds c a n (Fin.castLE hd i) (Fin.castLE hd i).isLt
  change |c.coord (reduceCoordinates c a n) (Fin.castLE hd i)| ≤ 1
  rw [abs_of_nonneg hi.1]
  exact hi.2.le

include hlin hΓ in
 

lemma canonical_representative_orbit (a : G) :
    let v:=fun h : ℕ => reduceCoordinates c (a^h) n
    (∀ h, ‖horizontal c hd (v h)‖≤1) ∧
    (∀ h, (v h)⁻¹*a^h∈Γ) ∧
    ∀ h,BracketHyperplanes.torusMap (horizontal c hd (v h))=
      BracketHyperplanes.torusMap (fun i => horizontal c hd a i*(h:ℝ)+(0:Fin d → ℝ) i) := by
  dsimp only
  have hv (h : ℕ) := reduceCoordinates_coset c Γ hΓ (a^h) n
  exact ⟨fun h => reduced_horizontal_bound c hd _,hv,
    representative_torus c hd hlin Γ hΓ a _ hv⟩

end MalcevHorizontal
end
end
 

 
section
noncomputable section
open scoped BigOperators commutatorElement
namespace MalcevHorizontal
open RationalLattice CubeFaces LeibmanSquare SquareHorizontalCharacter _root_.Polynomial _root_.OAI.Polynomial BracketDrift
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hlin hlevel hΓ in
 

theorem geometric_scalar_descent (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
    (Ξ : Finset (level H h0 1 →* Multiplicative ℝ)) (δ A : ℝ) (hδ : 0<δ) (hA : 0≤A) :
    ∃ R : ℕ, 0<R ∧ ∃ C : ℝ, 0<C ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀≤N → ∀ ξ∈Ξ, Continuous ξ →
      (∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z) →
      ∀ (f : ℤ → G) (hf : Polynomial H 0 f) (hf0 : f 0=1),
      ‖horizontal c hd (f 1)‖≤1 →
      ∀ v : ℕ → G, (∀ h, ‖horizontal c hd (v h)‖≤1) →
      (∀ h, (v h)⁻¹*f 1^h∈Γ) →
      ∀ S : Finset ℕ, S⊆Finset.range N → δ*N≤(S.card:ℝ) →
      (∀ h∈S, ∃ W : ℝ[X],
        (∀ z : ℤ, W.eval (z:ℝ)=
          (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h (v h) z)).toAdd) ∧
        ∀ j : ℕ, 0<j → j≤ s → ∃ m : ℤ, |W.coeff j-m|≤A/(N:ℝ)^j) →
      (∃ k : Fin d → ℤ, k≠0 ∧ (∀ i, |k i|≤R) ∧
        ∃ χ : G →* Multiplicative ℝ, χ=character c hd hlin k ∧ χ≠1 ∧ Continuous χ ∧
        (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 1 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ m : ℤ, |P.coeff j-m|≤C/(N:ℝ)^j) ∨
      ((∀ a b : G, pairing H h0 h1 ξ a b=1) ∧
        ∃ q : ℤ, q≠0 ∧ |q|≤R ∧ ∃ P Q : ℝ[X],
          P.natDegree ≤ s ∧ Q.natDegree ≤ s ∧ Q.eval 0=0 ∧ Q.eval 1=0 ∧
          (∀ z : ℤ, P.eval (z:ℝ)=((ξ.comp (diagonal H h0 h1)) (f z)).toAdd) ∧
          (∀ z : ℤ, Q.eval (z:ℝ)=((ξ.comp (lower H h0)) (linearRemainder H h0 hf hf0 z)).toAdd) ∧
          (∀ j : ℕ, 0<j → ∃ m : ℤ, |(q:ℝ)*P.coeff j-m|≤C/(N:ℝ)^j) ∧
          (∀ j : ℕ, 1<j → ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m|≤C/(N:ℝ)^j)) := by
  classical
  let B:=⌈squareMatrixBound c hd H h0 h1 Ξ⌉₊
  obtain ⟨R,hR,C,hC,N₀,hN₀,hdesc⟩ := NonabelianCharacterDescent.scalar_descent d s B hs2 δ A hδ hA
  refine ⟨R,hR,C,hC,N₀,hN₀,?_⟩
  intro N hNN ξ hξ hξc hξΓ f hf hf0 hf1 v hv hvΓ S hSN hS hsmall
  obtain ⟨M,hdiag,halt,hM⟩ := square_integer_matrix c hd hlin H h0 h1 hlevel ξ Γ hΓ hξc hξΓ
  have hMb (i j : Fin d) : |M i j|≤B := by
    have hb : |(M i j:ℝ)|≤(B:ℝ) :=
      (matrix_bound c hd H h0 h1 ξ M hM Ξ hξ i j).trans (Nat.le_ceil _)
    exact_mod_cast hb
  obtain ⟨P,Q,hP,hQ,hQ0,hQ1,hPe,hQe,hPQ⟩ :=
    exists_actual_square_polynomials H h0 h1 ξ s hs hf hf0
  have hm (h : ℕ) : (pairing H h0 h1 ξ (f 1) (v h)).toAdd=
      ∑ i,matrixContraction M (horizontal c hd (f 1)) i*horizontal c hd (v h) i := by
    rw [hM]
    simp only [matrixContraction,Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsmall' (h : ℕ) (hh : h∈S) (j : ℕ) (hj : 0<j) (hjs : j≤ s) :
      ∃ m : ℤ, |(P+taylor (h:ℝ) Q-Q).coeff j+
        (if j=1 then ∑ i,matrixContraction M (horizontal c hd (f 1)) i*horizontal c hd (v h) i else 0)-m|
          ≤ A/(N:ℝ)^j := by
    obtain ⟨W,hWe,hWc⟩ := hsmall h hh
    have he : W=P+taylor (h:ℝ) Q-Q+Polynomial.C ((pairing H h0 h1 ξ (f 1) (v h)).toAdd)*X := by
      apply Polynomial.eq_of_eval_nat_eq
      intro z
      simpa only [Int.cast_natCast] using (hWe (z:ℤ)).trans (hPQ (h:ℤ) (z:ℤ) (v h)).symm
    obtain ⟨m,hmc⟩ := hWc j hj hjs
    refine ⟨m,?_⟩
    rw [he,coeff_add,coeff_C_mul,coeff_X,hm] at hmc
    by_cases hj1 : j=1
    · simpa only [hj1,ite_true,mul_one] using hmc
    · simpa only [ite_eq_right hj1,ite_eq_right (Ne.symm hj1),mul_zero,add_zero] using hmc
  rcases hdesc N hNN M hMb (horizontal c hd (f 1)) 0 hf1
    (fun h => horizontal c hd (v h)) hv (representative_torus c hd hlin Γ hΓ (f 1) v hvΓ)
    P Q hP hQ S hSN hS hsmall' with hfirst | hzero
  · left
    obtain ⟨k,hk,hkR,m,hm⟩ := hfirst
    obtain ⟨χ,hχ0,hχc,hχΓ,hχk,P',hP',hPe',hPc'⟩ :=
      original_horizontal_obstruction c hd hlin H h0 hlevel Γ hΓ hf hf0 R N C hC.le k hk hkR m hm
    obtain ⟨k',hk'R,hχeq⟩ := hχk
    refine ⟨k',?_,hk'R,χ,hχeq,hχ0,hχc,hχΓ,P',hP',hPe',hPc'⟩
    intro hz
    apply hχ0
    rw [hχeq,hz]
    ext x
    simp [character]
  · right
    obtain ⟨hMz,q,hq,hqR,hPc,hQc⟩ := hzero
    exact ⟨(matrix_zero_iff c hd H h0 h1 ξ M hM).mp hMz,
      q,hq,hqR,P,Q,hP,hQ,hQ0,hQ1,hPe,hQe,hPc,hQc⟩

end MalcevHorizontal
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevTailSection
open RationalLattice MalcevCharacters IntegerHyperplane
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n) (hsk : SecondKind c)

def axisHom (i : Fin n) : Multiplicative ℝ →* G where
  toFun t := axis c i t.toAdd
  map_one' := axis_zero c i
  map_mul' s t := hsk.axis_add i s.toAdd t.toAdd

def HasPivot (k : Fin n → ℤ) (r : ℕ) : Prop := ∃ p : Fin n, r ≤ p.val ∧ k p ≠ 0

 

def tailSection (k : Fin n → ℤ) (r : ℕ) (t : ℝ) : G := by
  classical
  exact if h : HasPivot k r then axis c h.choose (t/(k h.choose:ℝ)) else 1

lemma section_zero (k : Fin n → ℤ) (r : ℕ) : tailSection c k r 0 = 1 := by
  classical
  unfold tailSection
  split_ifs <;> simp
include hsk in
lemma section_add (k : Fin n → ℤ) (r : ℕ) (s t : ℝ) :
    tailSection c k r (s+t) = tailSection c k r s * tailSection c k r t := by
  classical
  unfold tailSection
  split_ifs <;> simp [add_div,hsk.axis_add]

def flow (k : Fin n → ℤ) (r : ℕ) : Multiplicative ℝ →* G where
  toFun t := tailSection c k r t.toAdd
  map_one' := section_zero c k r
  map_mul' s t := section_add c hsk k r s.toAdd t.toAdd

include hsk in
lemma section_zpow (k : Fin n → ℤ) (r : ℕ) (t : ℝ) (z : ℤ) :
    tailSection c k r (z*t) = tailSection c k r t ^ z := by
  have h := (flow c hsk k r).map_zpow (Multiplicative.ofAdd t) z
  simpa [flow,zsmul_eq_mul] using h

lemma section_continuous (k : Fin n → ℤ) (r : ℕ) : Continuous (tailSection c k r) := by
  classical
  unfold tailSection
  split_ifs
  · exact (axis_continuous c _).comp (continuous_id.div_const _)
  · exact continuous_const

lemma section_tail (k : Fin n → ℤ) (r : ℕ) (t : ℝ) (i : Fin n) (hi : i.val < r) :
    c.coord (tailSection c k r t) i = 0 := by
  classical
  unfold tailSection
  split_ifs with h
  · rw [coord_axis]
    apply Pi.single_eq_of_ne
    intro he
    have := h.choose_spec.1
    subst i
    omega
  · exact c.one_coord i

lemma section_rational (k : Fin n → ℤ) (r : ℕ) (t : ℚ) :
    IsRational c (tailSection c k r t) := by
  classical
  intro i
  unfold tailSection
  split_ifs with h
  · refine ⟨if i=h.choose then t/(k h.choose:ℚ) else 0,?_⟩
    rw [coord_axis]
    simp only [Pi.single_apply]
    split_ifs <;> push_cast <;> rfl
  · exact ⟨0,by simpa using (c.one_coord i).symm⟩

lemma section_bound (k : Fin n → ℤ) (r : ℕ) (t : ℝ) (i : Fin n) :
    |c.coord (tailSection c k r t) i| ≤ |t| := by
  classical
  unfold tailSection
  split_ifs with h
  · rw [coord_axis]
    by_cases hi : i=h.choose
    · subst i
      rw [Pi.single_eq_same,abs_div]
      have hk : (1:ℝ) ≤ |(k h.choose:ℝ)| := by
        exact_mod_cast (Int.one_le_abs h.choose_spec.2)
      exact div_le_self (abs_nonneg t) hk
    · simp [Pi.single_eq_of_ne hi,abs_nonneg]
  · simp [c.one_coord,abs_nonneg]

lemma form_zero_of_no_pivot (k : Fin n → ℤ) (r : ℕ)
    (hk : ¬ HasPivot k r) (x : Fin n → ℝ) (hx : ∀ i, i.val < r → x i = 0) :
    form k x = 0 := by
  change (∑ i, (k i:ℝ)*x i) = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hir : i.val < r
  · rw [hx i hir,mul_zero]
  · have hi : k i = 0 := by by_contra he; exact hk ⟨i,by omega,he⟩
    simp [hi]

variable (χ : G →* Multiplicative ℝ) (k : Fin n → ℤ)
variable (hχ : ∀ g, (χ g).toAdd = form k (c.coord g))
include hχ in
lemma character_section (r : ℕ) (t : ℝ) (ht : ¬ HasPivot k r → t=0) :
    (χ (tailSection c k r t)).toAdd = t := by
  classical
  unfold tailSection
  split_ifs with h
  · rw [hχ,coord_axis]
    change (∑ i, (k i:ℝ)*(Pi.single h.choose (t/(k h.choose:ℝ)) : Fin n → ℝ) i) = t
    simp only [Pi.single_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact mul_div_cancel₀ t (by exact_mod_cast h.choose_spec.2)
  · rw [ht h]
    simp

end MalcevTailSection

end
end
end
end
end

end OAI
