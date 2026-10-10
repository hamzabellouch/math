import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare02
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare03
import OAI.Combinatorics.SumProduct.Alignment.PairTail05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement
noncomputable section
end
end
 

 
section
open scoped commutatorElement BigOperators
noncomputable section
namespace PairTail
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : Subgroup G) [K.Normal]
variable (η : square K →* Multiplicative ℝ)
variable (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ K)

def bracket (a b : G) : K := ⟨⁅a,b⁆,hcomm a b⟩

def bracketCharacter (a : G) : G →* Multiplicative ℝ where
  toFun b := lowerCharacter K η (bracket K hcomm a b)
  map_one' := by
    have he : bracket K hcomm a 1 = 1 := by apply Subtype.ext; simp [bracket]
    rw [he,map_one]
  map_mul' b c := by
    have he : bracket K hcomm a (b*c) = bracket K hcomm a b *
        ⟨b*(bracket K hcomm a c).val*b⁻¹,
          (inferInstance : K.Normal).conj_mem _ (bracket K hcomm a c).property b⟩ := by
      apply Subtype.ext
      change ⁅a,b*c⁆ = ⁅a,b⁆ * (b*⁅a,c⁆*b⁻¹)
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    rw [he,map_mul,lowerCharacter_conj]

lemma bracketCharacter_continuous (hη : Continuous η) (a : G) :
    Continuous (bracketCharacter K η hcomm a) := by
  apply (lowerCharacter_continuous K η hη).comp
  apply Continuous.subtype_mk
  exact ((continuous_const.mul continuous_id).mul continuous_const).mul continuous_inv

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma bracket_skew (a b : G) :
    lowerCharacter K η (bracket K hcomm b a) =
      (lowerCharacter K η (bracket K hcomm a b))⁻¹ := by
  have he : bracket K hcomm b a = (bracket K hcomm a b)⁻¹ := by
    apply Subtype.ext
    exact (commutatorElement_inv a b).symm
  rw [he,map_inv]

 

def leftBracketCharacter (b : G) : G →* Multiplicative ℝ :=
  (bracketCharacter K η hcomm b)⁻¹
lemma leftBracketCharacter_apply (a b : G) :
    leftBracketCharacter K η hcomm b a = lowerCharacter K η (bracket K hcomm a b) :=
  (bracket_skew K η hcomm b a).symm
lemma leftBracketCharacter_continuous (hη : Continuous η) (b : G) :
    Continuous (leftBracketCharacter K η hcomm b) :=
  (bracketCharacter_continuous K η hcomm hη b).inv

variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)

def bracketMatrix (i j : Fin n) : ℝ :=
  Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm (axis c i 1) (axis c j 1)))

include hsk in
 

lemma bracket_coordinates (hη : Continuous η) (a b : G) :
    Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm a b)) =
      ∑ i, ∑ j, c.coord a i * c.coord b j * bracketMatrix K η hcomm c i j := by
  have hright := character_coordinates c hsk (bracketCharacter K η hcomm a)
    (bracketCharacter_continuous K η hcomm hη a) b
  change Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm a b)) = _ at hright
  rw [hright]
  have hleft (j : Fin n) : Multiplicative.toAdd
      (bracketCharacter K η hcomm a (axis c j 1)) =
        ∑ i, c.coord a i * bracketMatrix K η hcomm c i j := by
    have he := character_coordinates c hsk (leftBracketCharacter K η hcomm (axis c j 1))
      (leftBracketCharacter_continuous K η hcomm hη (axis c j 1)) a
    simpa only [leftBracketCharacter_apply,bracketMatrix,bracketCharacter,MonoidHom.coe_mk,OneHom.coe_mk] using he
  simp_rw [hleft,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [IsTopologicalGroup G] in
lemma bracketMatrix_skew (i j : Fin n) :
    bracketMatrix K η hcomm c j i = - bracketMatrix K η hcomm c i j := by
  unfold bracketMatrix
  rw [bracket_skew]
  rfl
omit [IsTopologicalGroup G] in
lemma bracketMatrix_diagonal (i : Fin n) : bracketMatrix K η hcomm c i i = 0 := by
  have he := bracketMatrix_skew K η hcomm c i i
  linarith

variable (Γ : Subgroup G)
include hsk in
 

theorem integer_commutator_matrix (hη : Continuous η)
    (hletters : ∀ i : Fin n, axis c i 1 ∈ Γ)
    (hz : ∀ x ∈ squareLattice K Γ, ∃ z : ℤ, Multiplicative.toAdd (η x) = z) :
    ∃ M : Fin n → Fin n → ℤ,
      (∀ i j, (M i j : ℝ) = bracketMatrix K η hcomm c i j) ∧
      (∀ a b : G, Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm a b)) =
        ∑ i, ∑ j, c.coord a i * c.coord b j * (M i j : ℝ)) ∧
      (∀ i j, M j i = -M i j) ∧ (∀ i, M i i = 0) := by
  have hi (i j : Fin n) : ∃ z : ℤ, bracketMatrix K η hcomm c i j = z := by
    apply lowerCharacter_integral K η Γ hz (bracket K hcomm (axis c i 1) (axis c j 1))
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (hletters i) (hletters j)) (Γ.inv_mem (hletters i)))
      (Γ.inv_mem (hletters j))
  choose M hM using hi
  refine ⟨M,fun i j => (hM i j).symm,?_,?_,?_⟩
  · intro a b
    simpa only [hM] using bracket_coordinates K η hcomm c hsk hη a b
  · intro i j
    have he := bracketMatrix_skew K η hcomm c i j
    rw [hM,hM] at he
    exact_mod_cast he
  · intro i
    have he := bracketMatrix_diagonal K η hcomm c i
    rw [hM] at he
    exact_mod_cast he

end PairTail
end
end
 

 
section
noncomputable section
open scoped commutatorElement
namespace PairTail
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : Subgroup G) [K.Normal]
variable (η : square K →* Multiplicative ℝ)
variable (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ K)

def insideConj (a : G) (u : K) : K :=
  ⟨a*u*a⁻¹,(inferInstance : K.Normal).conj_mem _ u.property a⟩

lemma lower_insideConj (a : G) (u : K) :
    lowerCharacter K η (insideConj K a u) = lowerCharacter K η u :=
  lowerCharacter_conj K η a u

lemma bracket_inv_inv (a b : G) :
    lowerCharacter K η (bracket K hcomm a⁻¹ b⁻¹) =
      lowerCharacter K η (bracket K hcomm a b) := by
  change bracketCharacter K η hcomm a⁻¹ b⁻¹ = _
  rw [map_inv]
  change (lowerCharacter K η (bracket K hcomm a⁻¹ b))⁻¹ = _
  rw [← leftBracketCharacter_apply, map_inv, leftBracketCharacter_apply, inv_inv]

def normalizedTail (u w : K) (a v : G) : K :=
  insideConj K a⁻¹ u⁻¹ * insideConj K (a⁻¹*v⁻¹) w * bracket K hcomm a⁻¹ v⁻¹

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma normalizedTail_val (u w : K) (a v : G) :
    (normalizedTail K hcomm u w a v).val = (u.val*a)⁻¹*(v⁻¹*w.val*a*v) := by
  change (a⁻¹*u.val⁻¹*(a⁻¹)⁻¹)*((a⁻¹*v⁻¹)*w.val*(a⁻¹*v⁻¹)⁻¹)*
    ⁅a⁻¹,v⁻¹⁆ = _
  simp only [commutatorElement_def]
  group

lemma lower_normalizedTail (u w : K) (a v : G) :
    lowerCharacter K η (normalizedTail K hcomm u w a v) =
      (lowerCharacter K η u)⁻¹ * lowerCharacter K η w *
        lowerCharacter K η (bracket K hcomm a v) := by
  rw [normalizedTail,map_mul,map_mul,lower_insideConj,lower_insideConj,map_inv,
    bracket_inv_inv]

 

def normalizedPair (u w : K) (a v : G) : square K :=
  pair K (u.val*a) (normalizedTail K hcomm u w a v)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma normalizedPair_val (u w : K) (a v : G) :
    (normalizedPair K hcomm u w a v).val = (u.val*a,v⁻¹*w.val*a*v) := by
  ext
  · rfl
  · change (u.val*a)*(normalizedTail K hcomm u w a v).val = _
    rw [normalizedTail_val,mul_inv_cancel_left]

lemma normalizedPair_character (u w : K) (a v : G) :
    Multiplicative.toAdd (η (normalizedPair K hcomm u w a v)) =
      Multiplicative.toAdd (baseCharacter K η (u.val*a)) +
      Multiplicative.toAdd (lowerCharacter K η w) -
      Multiplicative.toAdd (lowerCharacter K η u) +
      Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm a v)) := by
  rw [character_split]
  change Multiplicative.toAdd (baseCharacter K η (u.val*a)) +
    Multiplicative.toAdd (lowerCharacter K η (difference K
      (pair K (u.val*a) (normalizedTail K hcomm u w a v)))) = _
  rw [difference_pair,lower_normalizedTail]
  simp only [toAdd_mul,toAdd_inv]
  ring

lemma bracket_zpow (a v : G) (n : ℤ) :
    Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm (a^n) v)) =
      (n:ℝ)*Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm a v)) := by
  rw [← leftBracketCharacter_apply,map_zpow,leftBracketCharacter_apply]
  simp only [toAdd_zpow,zsmul_eq_mul]

 

theorem square_orbit_identity (a v : G) (u : ℤ → K) (h n : ℤ) :
    Multiplicative.toAdd (η (normalizedPair K hcomm (u n) (u (n+h)) (a^n) v)) =
      Multiplicative.toAdd (baseCharacter K η ((u n).val*a^n)) +
      (Multiplicative.toAdd (lowerCharacter K η (u (n+h))) -
       Multiplicative.toAdd (lowerCharacter K η (u n))) +
      (n:ℝ)*Multiplicative.toAdd (lowerCharacter K η (bracket K hcomm a v)) := by
  rw [normalizedPair_character,bracket_zpow]
  ring

end PairTail
end
end
 

 
section
noncomputable section
open scoped commutatorElement ComplexConjugate
namespace LeibmanSquare
open CubeFaces CubePolynomials
variable {G : Type*} [Group G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)

include h0 in
 

lemma linear_remainder_mem {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1) (n : ℤ) :
    f n*(f 1^n)⁻¹∈H.level 2 := by
  let := level_normal H h0 2
  let π:=QuotientGroup.mk' (H.level 2)
  have hadd (a b : ℤ) : π (f (a+b))=π (f a)*π (f b) := by
    have hm := hf [b,a] 0
    have hz : π (iterDiff [b,a] f 0)=1 := (QuotientGroup.eq_one_iff _).mpr hm
    simp only [iterDiff,diff,zero_add,hf0,inv_one,one_mul,map_mul,map_inv] at hz
    have he := congrArg (fun x => π (f a)*π (f b)*x) hz
    convert he using 1 <;> group
  let φ : Multiplicative ℤ →* G ⧸ H.level 2 := {
    toFun z := π (f z.toAdd)
    map_one' := by change π (f 0)=1; rw [hf0,map_one]
    map_mul' a b := hadd a.toAdd b.toAdd }
  have he : (Multiplicative.ofAdd (1:ℤ))^n=Multiplicative.ofAdd n := by
    apply Multiplicative.toAdd.injective
    simp
  have hn : π (f n)=π (f 1)^n := by
    simpa [φ] using map_zpow φ (Multiplicative.ofAdd (1:ℤ)) n
  apply (QuotientGroup.eq_one_iff _).mp
  change π (f n*(f 1^n)⁻¹)=1
  rw [map_mul,map_inv,map_zpow,hn,mul_inv_cancel]

def linearRemainder {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1) (n : ℤ) : H.level 2 :=
  ⟨f n*(f 1^n)⁻¹,linear_remainder_mem H h0 hf hf0 n⟩

lemma linearRemainder_mul {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1) (n : ℤ) :
    f n=(linearRemainder H h0 hf hf0 n).val*f 1^n := by
  simp [linearRemainder,mul_assoc]

 
def tailSquare (u : H.level 2) : level H h0 1 :=
  ⟨(1,u.val),by
    refine ⟨(H.level 1).one_mem,?_,?_⟩
    · rw [h1]; trivial
    · simp⟩

def linearNormalizedPair {f : ℤ → G} (hf : Polynomial H 0 f)
    (u : H.level 2) (h : ℤ) (v : G) : ℤ → level H h0 1 := fun n =>
  restrictedConj H h0 h1 1 v⁻¹
    (restrictedConj H h0 h1 1 (f h) (normalizedPair H h0 hf h n) * tailSquare H h0 h1 u)

lemma linearNormalizedPair_polynomial {f : ℤ → G} (hf : Polynomial H 0 f)
    (u : H.level 2) (h : ℤ) (v : G) :
    Polynomial (restricted H h0) 0 (linearNormalizedPair H h0 h1 hf u h v) := by
  apply polynomial_filtered_map _ _ _ (restrictedConj_filtered H h0 h1 1 v⁻¹)
  apply polynomial_of_cube_mem
  exact (polynomials (restricted H h0) 0).mul_mem
    (cube_mem_of_polynomial _ (normalized_conjugate_polynomial H h0 h1 hf h 1 (f h)))
    (const_mem (by rw [restricted_zero]; trivial))

lemma linearNormalizedPair_val {f : ℤ → G} (hf : Polynomial H 0 f)
    (hf0 : f 0=1) (a : G) (u : H.level 2) (h : ℤ) (v : G)
    (huh : f h=u.val*a^h) (n : ℤ) :
    (linearNormalizedPair H h0 h1 hf u h v n).val =
      (f n,v⁻¹*f (n+h)*(a^h)⁻¹*v) := by
  change (1*(1*((f 0)⁻¹*f n)*1⁻¹*1)*1⁻¹,
    v⁻¹*((f h*((f h)⁻¹*f (n+h))*(f h)⁻¹)*u.val)*(v⁻¹)⁻¹)=_
  simp only [hf0,inv_one,one_mul,mul_one,inv_inv,huh,mul_inv_rev]
  congr 1
  group

lemma linearNormalizedPair_reduced {f : ℤ → G} (hf : Polynomial H 0 f)
    (u : H.level 2) (h : ℤ) (v : G) {s : ℕ} (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥) :
    letI := last_normal H h0 hs0 hs
    let π:=QuotientGroup.mk' ((restricted H h0).level s)
    let Q:=mapFiltration (restricted H h0) π
    let p:=fun n => π (linearNormalizedPair H h0 h1 hf u h v n)
    Polynomial Q 0 p ∧ ∀ ts : List ℤ, s≤ts.length → ∀ n, iterDiff ts p n=1 := by
  dsimp only
  let := last_normal H h0 hs0 hs
  have hp:=polynomial_map _ (QuotientGroup.mk' ((restricted H h0).level s))
    (linearNormalizedPair_polynomial H h0 h1 hf u h v)
  refine ⟨hp,?_⟩
  intro ts hts n
  have hm := (mapFiltration (restricted H h0) (QuotientGroup.mk' ((restricted H h0).level s))).antitone
    (by omega : s≤0+ts.length) (hp ts n)
  simpa only [(quotient_lowers_degree H h0 hs0 hs).2.2,Subgroup.mem_bot] using hm

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
lemma balanced_linearNormalizedPair (Γ : Subgroup G) (F : C(G ⧸ Γ,ℂ))
    {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1) (a : G)
    (u : H.level 2) (h : ℤ) (v γ : G) (hγ : γ∈Γ) (hav : a^h=v*γ)
    (huh : f h=u.val*a^h) (n : ℤ) :
    balanced H h0 Γ F 1 v (linearNormalizedPair H h0 h1 hf u h v n)=
      F (QuotientGroup.mk (f n))*conj (F (QuotientGroup.mk (f (n+h)))) := by
  unfold balanced
  rw [linearNormalizedPair_val H h0 h1 hf hf0 a u h v huh n]
  simp only [one_mul]
  have he : v*(v⁻¹*f (n+h)*(a^h)⁻¹*v)=f (n+h)*γ⁻¹ := by rw [hav]; group
  rw [he,QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem hγ)]

variable [∀ i, (H.level i).Normal]

 

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma linearNormalizedPair_eq_pairTail {f : ℤ → G} (hf : Polynomial H 0 f)
    (hf0 : f 0=1) (a : G) (u : ℤ → H.level 2) (hu : ∀ n, f n=(u n).val*a^n)
    (hcomm : ∀ a b : G, ⁅a,b⁆∈H.level 2) (h n : ℤ) (v : G) :
    firstPairEquiv H h0 h1 (linearNormalizedPair H h0 h1 hf (u h) h v n)=
      PairTail.normalizedPair (H.level 2) hcomm (u n) (u (n+h)) (a^n) v := by
  apply Subtype.ext
  rw [firstPairEquiv_val,linearNormalizedPair_val H h0 h1 hf hf0 a (u h) h v (hu h) n,
    PairTail.normalizedPair_val,hu n,hu (n+h),zpow_add]
  congr 1
  group

end LeibmanSquare

end
end
end
end
end

end OAI
