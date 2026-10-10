import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BinomialDifference01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
noncomputable section
end
end
 

 
section
open scoped BigOperators commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace CharacterFactorization
open CubeFaces CubePolynomials RationalFactorPeriods RationalLattice MalcevCharacters MalcevTailFactor
open LeibmanSquare
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable (H : Filtration G) (h0 : H.level 0=⊤) {n s : ℕ}
variable (c : RealCoordinates (H.level 2) n) (hsk : SecondKind c)
variable (χ : H.level 2 →* Multiplicative ℝ) (k : Fin n → ℤ)
variable (hχ : ∀ x, (χ x).toAdd = IntegerHyperplane.form k (c.coord x))
variable (r : Fin s → ℕ)
variable (hlevel : ∀ i (x : H.level 2), x.val ∈ H.level (i.val+2) ↔
  ∀ u : Fin n, u.val < r i → c.coord x u = 0)
variable (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ χ.ker.map (H.level 2).subtype)

include hsk hχ hlevel in
 

theorem factorization_from_monomial_bounds (hbot : H.level s=⊥)
    (Γ : Subgroup G) (hΓ : ∀ x : H.level 2, x.val∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord x i=z)
    (d : ℕ) (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∃ T : ℕ, 0<T ∧
      ∀ (L : ℝ), 1 ≤ L →
      ∀ (f : ℤ → G) (hf : Polynomial H 0 f) (hf0 : f 0=1), f 1∈H.level 1 →
      ∀ P : ℝ[X], P.natDegree ≤ d →
      (∀ z : ℤ, P.eval (z:ℝ)=(χ (linearRemainder H h0 hf hf0 z)).toAdd) →
      (∀ j : ℕ, 1<j → ∃ m : ℤ, |P.coeff j-m| ≤ C/L^j) →
      ∃ e b : ℤ → H.level 2, ∃ f' : ℤ → G,
        (∀ z, f z=(e z).val*f' z*(b z).val) ∧ e 0=1 ∧
        (fun z => (e z).val) ∈ polynomials H 0 ∧
        (fun z => (b z).val) ∈ polynomials H 0 ∧
        f' ∈ polynomials (H.refine (χ.ker.map (H.level 2).subtype) hcomm) 0 ∧
        Function.Periodic (fun z => (QuotientGroup.mk (b z).val : G ⧸ Γ)) (T:ℤ) ∧
        (∀ z : ℤ, |(z:ℝ)| ≤ A*L → ‖c.coord (e z)‖ ≤ B) ∧
        (∀ z w : ℤ, |(z:ℝ)| ≤ A*L → |(w:ℝ)| ≤ A*L →
          ‖c.coord (e z*(e w)⁻¹)‖ ≤ (B/L)*|(z:ℝ)-(w:ℝ)|) := by
  obtain ⟨B,hB,T,hT,hfactor⟩ := uniform_smooth_factorization H c hsk χ k hχ r hlevel hcomm
    hbot Γ hΓ A (BinomialDifference.conversionBound d*C)
    (mul_nonneg (BinomialDifference.conversionBound_pos d).le hC)
  refine ⟨B,hB,T,hT,?_⟩
  intro L hL f hf hf0 hf1 P hP hPe hPc
  obtain ⟨a,ha,he,hfac,he0,hep,hbp,hfp,hper,hsmooth⟩ := hfactor f
    (cube_mem_of_polynomial H hf) hf0 hf1
  have hword (z : ℤ) : P.eval (z:ℝ)=(χ (orderedWord a (fun i => i.val+2) z)).toAdd := by
    rw [hPe]
    congr 2
    apply Subtype.ext
    change f z*(f 1^z)⁻¹=(orderedWord a (fun i => i.val+2) z).val
    rw [he z]
    group
  have hb : ∀ i, L^(i.val+2)*‖(beta χ a i : UnitAddCircle)‖ ≤ BinomialDifference.conversionBound d*C :=
    BinomialDifference.word_coefficient_bound χ a 2 d P hP hword L C hL hC (fun j hj => hPc j (by omega))
  obtain ⟨hv,hdiff⟩ := hsmooth L hL hb
  refine ⟨(fun z => orderedWord (smallCoeff c χ k r a) (fun i => i.val+2) z),
    (fun z => orderedWord (rationalCoeff c χ k r a) (fun i => i.val+2) z),
    residual H c χ k r f a,hfac,?_,hep,hbp,hfp,hper,hv,hdiff⟩
  apply Subtype.ext
  exact he0

end CharacterFactorization
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators commutatorElement
namespace RealCharacters
variable {G : Type*} [Group G]
def intScale (χ : G →* Multiplicative ℝ) (q : ℤ) : G →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd ((q:ℝ)*(χ x).toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]
@[simp] lemma intScale_apply (χ : G →* Multiplicative ℝ) (q : ℤ) (x : G) :
    (intScale χ q x).toAdd=(q:ℝ)*(χ x).toAdd := rfl
lemma intScale_continuous [TopologicalSpace G] (χ : G →* Multiplicative ℝ)
    (q : ℤ) (hχ : Continuous χ) : Continuous (intScale χ q) := by
  change Continuous (fun x : G => (q:ℝ)*(χ x).toAdd)
  exact continuous_const.mul (show Continuous (fun x => (χ x).toAdd) from hχ)
lemma intScale_ne_one (χ : G →* Multiplicative ℝ) {q : ℤ} (hq : q≠0) (hχ : χ≠1) :
    intScale χ q≠1 := by
  intro hh
  apply hχ
  apply MonoidHom.ext
  intro x
  apply Multiplicative.toAdd.injective
  have hx := congrArg (fun f : G →* Multiplicative ℝ => (f x).toAdd) hh
  change (q:ℝ)*(χ x).toAdd=0 at hx
  simpa only [MonoidHom.one_apply,toAdd_one] using (mul_eq_zero.mp hx).resolve_left (Int.cast_ne_zero.mpr hq)
lemma intScale_integral (χ : G →* Multiplicative ℝ) (q : ℤ) (Γ : Subgroup G)
    (hχ : ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z) :
    ∀ g∈Γ, ∃ z : ℤ, (intScale χ q g).toAdd=z := by
  intro g hg
  obtain ⟨z,hz⟩ := hχ g hg
  exact ⟨q*z,by simp only [intScale_apply,hz,Int.cast_mul]⟩
lemma intScale_kernel (χ : G →* Multiplicative ℝ) {q : ℤ} (hq : q≠0) :
    (intScale χ q).ker=χ.ker := by
  ext x
  constructor
  · intro hx
    apply Multiplicative.toAdd.injective
    have hh:=congrArg Multiplicative.toAdd hx
    change (q:ℝ)*(χ x).toAdd=0 at hh
    exact (mul_eq_zero.mp hh).resolve_left (Int.cast_ne_zero.mpr hq)
  · intro hx
    change Multiplicative.ofAdd ((q:ℝ)*(χ x).toAdd)=1
    change χ x=1 at hx
    simp [hx]
end RealCharacters

namespace SquareHorizontalCharacter
open CubeFaces LeibmanSquare RealCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (ξ : level H h0 1 →* Multiplicative ℝ)
omit [IsTopologicalGroup G] in
lemma diagonal_continuous : Continuous (diagonal H h0 h1) :=
  (continuous_id.prodMk continuous_id).subtype_mk _
omit [IsTopologicalGroup G] in
lemma lower_continuous : Continuous (lower H h0) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma diagonal_integral (Γ : Subgroup G)
    (hξ : ∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z) :
    ∀ g∈Γ, ∃ z : ℤ, ((ξ.comp (diagonal H h0 h1)) g).toAdd=z := by
  intro g hg
  exact hξ _ ⟨hg,hg⟩
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma lower_integral (Γ : Subgroup G)
    (hξ : ∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z) :
    ∀ u : H.level 2, u.val∈Γ → ∃ z : ℤ, ((ξ.comp (lower H h0)) u).toAdd=z := by
  intro u hu
  exact hξ _ ⟨Γ.one_mem,hu⟩
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma lower_ne_one_of_diagonal (hξ : ξ≠1) (hd : ξ.comp (diagonal H h0 h1)=1) :
    ξ.comp (lower H h0)≠1 := by
  intro hl
  apply hξ
  ext x
  rw [character_split H h0 h1 ξ x,hd,hl]
  simp
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma zero_pairing_kernel (q : ℤ) (hp : ∀ a b : G, pairing H h0 h1 ξ a b=1) :
    ∀ a b : G, ⁅a,b⁆∈(intScale (ξ.comp (lower H h0)) q).ker.map (H.level 2).subtype := by
  intro a b
  refine ⟨⟨⁅a,b⁆,commutator_mem H h1 a b⟩,?_,rfl⟩
  change Multiplicative.ofAdd ((q:ℝ)*(pairing H h0 h1 ξ a b).toAdd)=1
  simp [hp]

end SquareHorizontalCharacter

namespace CharacterFactorization
open CubeFaces
variable {G : Type*} [Group G]
variable (H : Filtration G) (χ : H.level 2 →* Multiplicative ℝ)
lemma lower_kernel_le : χ.ker.map (H.level 2).subtype ≤ H.level 2 := by
  rintro g ⟨u,hu,rfl⟩
  exact u.property
lemma lower_kernel_lt (hχ : χ≠1) : χ.ker.map (H.level 2).subtype < H.level 2 := by
  refine lt_iff_le_not_ge.mpr ⟨lower_kernel_le H χ,?_⟩
  intro hh
  apply hχ
  apply MonoidHom.ext
  intro u
  obtain ⟨v,hv,hvu⟩ := hh u.property
  have hvu' : v=u := Subtype.ext hvu
  change χ u=1
  change χ v=1 at hv
  simpa only [hvu'] using hv

end CharacterFactorization
end
end
 

 
section
open scoped BigOperators commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace CharacterFactorization
open CubeFaces CubePolynomials RationalLattice MalcevCharacters LeibmanSquare
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable (H : Filtration G) (Γ : Subgroup G) {n : ℕ} (c : RealCoordinates (H.level 2) n)

 

def SmoothFactorizationAt (χ : H.level 2 →* Multiplicative ℝ)
    (hcomm : ∀ a b : G, ⁅a,b⁆∈χ.ker.map (H.level 2).subtype)
    (A B L : ℝ) (T : ℕ) (f : ℤ → G) : Prop :=
  ∃ e b : ℤ → H.level 2, ∃ f' : ℤ → G,
    (∀ z, f z=(e z).val*f' z*(b z).val) ∧ e 0=1 ∧
    (fun z => (e z).val) ∈ polynomials H 0 ∧
    (fun z => (b z).val) ∈ polynomials H 0 ∧
    f' ∈ polynomials (H.refine (χ.ker.map (H.level 2).subtype) hcomm) 0 ∧
    Function.Periodic (fun z => (QuotientGroup.mk (b z).val : G ⧸ Γ)) (T:ℤ) ∧
    (∀ z : ℤ, |(z:ℝ)| ≤ A*L → ‖c.coord (e z)‖ ≤ B) ∧
    (∀ z w : ℤ, |(z:ℝ)| ≤ A*L → |(w:ℝ)| ≤ A*L →
      ‖c.coord (e z*(e w)⁻¹)‖ ≤ (B/L)*|(z:ℝ)-(w:ℝ)|)

omit [IsTopologicalGroup G] [T2Space G] in
lemma SmoothFactorizationAt.mono {χ : H.level 2 →* Multiplicative ℝ}
    {hc : ∀ a b : G, ⁅a,b⁆∈χ.ker.map (H.level 2).subtype}
    {A B B' L : ℝ} {T : ℕ} {f : ℤ → G} (hL : 0 ≤ L) (hB : B ≤ B')
    (h : SmoothFactorizationAt H Γ c χ hc A B L T f) :
    SmoothFactorizationAt H Γ c χ hc A B' L T f := by
  obtain ⟨e,b,f',he,he0,hep,hbp,hfp,hper,hv,hd⟩ := h
  refine ⟨e,b,f',he,he0,hep,hbp,hfp,hper,fun z hz => (hv z hz).trans hB,?_⟩
  intro z w hz hw
  exact (hd z w hz hw).trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hB hL) (abs_nonneg _))

variable (h0 : H.level 0=⊤) (hsk : SecondKind c)
variable (hΓ : ∀ x : H.level 2, x.val∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord x i=z)
variable {s : ℕ} (hbot : H.level s=⊥) (r : Fin s → ℕ)
variable (hlevel : ∀ i (x : H.level 2), x.val∈H.level (i.val+2) ↔
  ∀ u : Fin n, u.val<r i → c.coord x u=0)

include hsk hΓ hbot hlevel in
 

theorem finite_lower_factorizations
    (Ξ : Finset (H.level 2 →* Multiplicative ℝ))
    (hcont : ∀ χ∈Ξ, Continuous χ)
    (hint : ∀ χ∈Ξ, ∀ x : H.level 2, x.val∈Γ → ∃ z : ℤ, (χ x).toAdd=z)
    (d : ℕ) (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0<B ∧ ∃ Tmax : ℕ, 0<Tmax ∧
      ∀ χ∈Ξ, ∀ hc : ∀ a b : G, ⁅a,b⁆∈χ.ker.map (H.level 2).subtype,
      ∀ (L : ℝ), 1 ≤ L →
      ∀ (f : ℤ → G) (hf : Polynomial H 0 f) (hf0 : f 0=1), f 1∈H.level 1 →
      ∀ P : ℝ[X], P.natDegree ≤ d →
      (∀ z : ℤ, P.eval (z:ℝ)=(χ (linearRemainder H h0 hf hf0 z)).toAdd) →
      (∀ j : ℕ, 1<j → ∃ m : ℤ, |P.coeff j-m| ≤ C/L^j) →
      ∃ T : ℕ, 0<T ∧ T ≤ Tmax ∧ SmoothFactorizationAt H Γ c χ hc A B L T f := by
  classical
  have hindividual (χ : {χ // χ∈Ξ}) :
      ∃ B : ℝ, 0<B ∧ ∃ T : ℕ, 0<T ∧
        ∀ hc : ∀ a b : G, ⁅a,b⁆∈χ.val.ker.map (H.level 2).subtype,
        ∀ (L : ℝ), 1 ≤ L →
        ∀ (f : ℤ → G) (hf : Polynomial H 0 f) (hf0 : f 0=1), f 1∈H.level 1 →
        ∀ P : ℝ[X], P.natDegree ≤ d →
        (∀ z : ℤ, P.eval (z:ℝ)=(χ.val (linearRemainder H h0 hf hf0 z)).toAdd) →
        (∀ j : ℕ, 1<j → ∃ m : ℤ, |P.coeff j-m| ≤ C/L^j) →
        SmoothFactorizationAt H Γ c χ.val hc A B L T f := by
    by_cases hc : ∀ a b : G, ⁅a,b⁆∈χ.val.ker.map (H.level 2).subtype
    · obtain ⟨k,hk⟩ := integer_character_coordinates c hsk χ.val (Γ.comap (H.level 2).subtype)
        hΓ (hcont χ.val χ.property) (hint χ.val χ.property)
      have hk' (x : H.level 2) : (χ.val x).toAdd=IntegerHyperplane.form k (c.coord x) := by
        simpa only [IntegerHyperplane.form,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using hk x
      obtain ⟨B,hB,T,hT,hfac⟩ := factorization_from_monomial_bounds H h0 c hsk χ.val k hk' r hlevel hc
        hbot Γ hΓ d A C hC
      exact ⟨B,hB,T,hT,fun _ => hfac⟩
    · exact ⟨1,by norm_num,1,by norm_num,fun hc' => (hc hc').elim⟩
  choose B hB T hT hfac using hindividual
  let Bsum : ℝ := 1+∑ χ : {χ // χ∈Ξ}, B χ
  let Tmax : ℕ := 1+∑ χ : {χ // χ∈Ξ}, T χ
  have hBsum : 0<Bsum := by
    have hh : 0 ≤ ∑ χ : {χ // χ∈Ξ}, B χ := Finset.sum_nonneg (fun χ _ => (hB χ).le)
    change 0 < 1+∑ χ : {χ // χ∈Ξ}, B χ
    linarith
  refine ⟨Bsum,hBsum,Tmax,by change 0 < 1+∑ χ : {χ // χ∈Ξ}, T χ; omega,?_⟩
  intro χ hχ hc L hL f hf hf0 hf1 P hP hPe hPc
  let j : {χ // χ∈Ξ} := ⟨χ,hχ⟩
  have hBB : B j ≤ Bsum := by
    have hh := Finset.single_le_sum (fun χ (_ : χ∈Finset.univ) => (hB χ).le) (Finset.mem_univ j)
    change B j ≤ 1+∑ χ : {χ // χ∈Ξ}, B χ
    linarith
  have hTT : T j ≤ Tmax := by
    have hh := Finset.single_le_sum (fun χ (_ : χ∈Finset.univ) => Nat.zero_le (T χ)) (Finset.mem_univ j)
    change T j ≤ 1+∑ χ : {χ // χ∈Ξ}, T χ
    omega
  exact ⟨T j,hT j,hTT,(hfac j hc L hL f hf hf0 hf1 P hP hPe hPc).mono H Γ c
    (zero_le_one.trans hL) hBB⟩

end CharacterFactorization

end
end
end
end
end

end OAI
