import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PairTail06
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped commutatorElement ComplexConjugate
end
end
 

 
section
noncomputable section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial Finset
namespace RationalFactorPeriods

def choosePolynomial (j : ℕ) : ℝ[X] := C (j.factorial:ℝ)⁻¹*descPochhammer ℝ j

lemma choosePolynomial_eval (j : ℕ) (x : ℝ) :
    (choosePolynomial j).eval x=Ring.choose x j := by
  rw [choosePolynomial,eval_mul,eval_C,Ring.choose_eq_smul,smul_eq_mul,
    ← aeval_eq_smeval,aeval_def,← eval_map,descPochhammer_map]

lemma choosePolynomial_int (j : ℕ) (n : ℤ) :
    (choosePolynomial j).eval (n:ℝ)=(Ring.choose n j:ℤ) := by
  rw [choosePolynomial_eval]
  exact (Ring.map_choose (Int.castRingHom ℝ) n j).symm

lemma choosePolynomial_natDegree (j : ℕ) : (choosePolynomial j).natDegree ≤ j := by
  calc
    _  ≤  (C (j.factorial:ℝ)⁻¹).natDegree+(descPochhammer ℝ j).natDegree := natDegree_mul_le
    _ = j := by rw [natDegree_C,descPochhammer_natDegree,zero_add]

variable {G : Type*} [Group G]
def wordCharacterPolynomial {l : ℕ} (χ : G →* Multiplicative ℝ)
    (a : Fin l → G) (j : Fin l → ℕ) : ℝ[X] :=
  ∑ i, C ((χ (a i)).toAdd)*choosePolynomial (j i)

lemma wordCharacterPolynomial_eval {l : ℕ} (χ : G →* Multiplicative ℝ)
    (a : Fin l → G) (j : Fin l → ℕ) (n : ℤ) :
    (wordCharacterPolynomial χ a j).eval (n:ℝ)=(χ (orderedWord a j n)).toAdd := by
  rw [wordCharacterPolynomial,eval_finsetSum,orderedWord_character]
  apply sum_congr rfl
  intro i _
  rw [eval_mul,eval_C,choosePolynomial_int,mul_comm]

lemma wordCharacterPolynomial_degree {l : ℕ} (χ : G →* Multiplicative ℝ)
    (a : Fin l → G) (j : Fin l → ℕ) (s : ℕ)
    (h : ∀ i, j i ≤ s ∨ χ (a i)=1) : (wordCharacterPolynomial χ a j).natDegree ≤ s := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  rcases h i with hi | hi
  · exact (natDegree_mul_le.trans (by
      simpa only [natDegree_C,zero_add] using choosePolynomial_natDegree (j i))).trans hi
  · simpa only [hi,toAdd_one,C_0,zero_mul,natDegree_zero] using Nat.zero_le s
end RationalFactorPeriods

namespace LeibmanSquare
open CubeFaces CubePolynomials RationalFactorPeriods
variable {G : Type*} [Group G]
variable (H : Filtration G) (h0 : H.level 0=⊤)

 

lemma character_polynomial (s : ℕ) (hs : H.level (s+1)=⊥)
    {f : ℤ → G} (hf : Polynomial H 0 f) (χ : G →* Multiplicative ℝ) :
    ∃ P : ℝ[X], P.natDegree ≤ s ∧ ∀ n : ℤ, P.eval (n:ℝ)=(χ (f n)).toAdd := by
  obtain ⟨a,ha,he⟩ := NilpotentTaylor.exists_taylor (by simpa using hs)
    (cube_mem_of_polynomial H hf)
  rw [word_eq_orderedWord] at he
  refine ⟨wordCharacterPolynomial χ (fun i : Fin (s+1) => a i.val) (fun i => i.val),
    wordCharacterPolynomial_degree _ _ _ s (fun i => Or.inl (by omega)),?_⟩
  intro n
  rw [wordCharacterPolynomial_eval]
  exact congrArg (fun z => (χ (z n)).toAdd) he.symm

 

lemma remainder_character_polynomial (h1 : H.level 1=⊤) (s : ℕ)
    (hs : H.level (s+1)=⊥) {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1)
    (χ : H.level 2 →* Multiplicative ℝ) :
    ∃ Q : ℝ[X], Q.natDegree ≤ s ∧ Q.eval 0=0 ∧ Q.eval 1=0 ∧
      ∀ n : ℤ, Q.eval (n:ℝ)=(χ (linearRemainder H h0 hf hf0 n)).toAdd := by
  obtain ⟨a,ha,he⟩ := NilpotentTaylor.normalized_subgroup_taylor H (s+1) hs f
    (cube_mem_of_polynomial H hf) hf0 (by rw [h1]; trivial)
  have ha' (i : Fin (s+1)) : i.val+2 ≤ s ∨ χ (a i)=1 := by
    by_cases hi : i.val+2 ≤ s
    · exact Or.inl hi
    · right
      have hz : a i=1 := by
        apply Subtype.ext
        change (a i).val=1
        have hm := H.antitone (by omega : s+1 ≤ i.val+2) (ha i)
        simpa only [hs,Subgroup.mem_bot] using hm
      rw [hz,map_one]
  let Q:=wordCharacterPolynomial χ a (fun i => i.val+2)
  have hQ (n : ℤ) : Q.eval (n:ℝ)=(χ (linearRemainder H h0 hf hf0 n)).toAdd := by
    rw [wordCharacterPolynomial_eval]
    congr 2
    apply Subtype.ext
    change (orderedWord a (fun i => i.val+2) n).val=f n*(f 1^n)⁻¹
    rw [he n]
    group
  refine ⟨Q,wordCharacterPolynomial_degree _ _ _ s ha',?_,?_,hQ⟩
  · have he0 : linearRemainder H h0 hf hf0 0=1 := by
      apply Subtype.ext
      change f 0*(f 1^(0:ℤ))⁻¹=1
      simp [hf0]
    simpa only [Int.cast_zero,he0,map_one,toAdd_one] using hQ 0
  · have he1 : linearRemainder H h0 hf hf0 1=1 := by
      apply Subtype.ext
      change f 1*(f 1^(1:ℤ))⁻¹=1
      simp
    simpa only [Int.cast_one,he1,map_one,toAdd_one] using hQ 1

end LeibmanSquare
end
end
 

 
section
open scoped commutatorElement
namespace SquareHorizontalCharacter
open CubeFaces LeibmanSquare
variable {G K : Type*} [Group G] [CommGroup K]
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)

 
def diagonal : G →* level H h0 1 where
  toFun g := ⟨(g,g), by simp [mem_level,h1]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

 
def lower : H.level 2 →* level H h0 1 where
  toFun u := ⟨(1,u), by
    refine ⟨(H.level 1).one_mem,H.antitone (by omega) u.property,?_⟩
    simp⟩
  map_one' := rfl
  map_mul' u v := by apply Subtype.ext; ext <;> simp

 
def tail (x : level H h0 1) : H.level 2 := ⟨x.val.1⁻¹*x.val.2,x.property.2.2⟩

lemma split (x : level H h0 1) :
    diagonal H h0 h1 x.val.1 * lower H h0 (tail H h0 x) = x := by
  apply Subtype.ext
  ext <;> simp [diagonal,lower,tail]

variable (ξ : level H h0 1 →* K)

 

theorem character_split (x : level H h0 1) :
    ξ x = (ξ.comp (diagonal H h0 h1)) x.val.1 *
      (ξ.comp (lower H h0)) (tail H h0 x) := by
  simp only [MonoidHom.comp_apply,← map_mul,split H h0 h1]

include h1

lemma lower_conj (g : G) (u : H.level 2) :
    ξ (lower H h0 ⟨g*u*g⁻¹,(level_normal H h0 2).conj_mem _ u.property g⟩) =
      ξ (lower H h0 u) := by
  have he : lower H h0 ⟨g*u*g⁻¹,(level_normal H h0 2).conj_mem _ u.property g⟩ =
      diagonal H h0 h1 g * lower H h0 u * (diagonal H h0 h1 g)⁻¹ := by
    apply Subtype.ext
    ext <;> simp [diagonal,lower]
  rw [he,map_mul,map_mul,map_inv]
  calc
    _ = ξ (lower H h0 u) * (ξ (diagonal H h0 h1 g) * (ξ (diagonal H h0 h1 g))⁻¹) := by ac_rfl
    _ = _ := by simp

 
lemma commutator_mem (a b : G) : ⁅a,b⁆ ∈ H.level 2 := by
  apply H.commutator_le 1 1
  apply Subgroup.commutator_mem_commutator <;> rw [h1] <;> trivial

 
def pairing (a b : G) : K :=
  ξ (lower H h0 ⟨⁅a,b⁆,commutator_mem H h1 a b⟩)

lemma lower_commutator (g : G) (u : H.level 2) :
    ξ (lower H h0 ⟨⁅g,(u:G)⁆,commutator_mem H h1 g u⟩) = 1 := by
  have he : (⟨⁅g,(u:G)⁆,commutator_mem H h1 g u⟩ : H.level 2) =
      ⟨g*u*g⁻¹,(level_normal H h0 2).conj_mem _ u.property g⟩ * u⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [he,map_mul,map_inv,map_mul,map_inv,lower_conj H h0 h1 ξ, mul_inv_cancel]

 

lemma pairing_mul_right (a b c : G) :
    pairing H h0 h1 ξ a (b*c) = pairing H h0 h1 ξ a b * pairing H h0 h1 ξ a c := by
  let u : H.level 2 := ⟨⁅a,c⁆,commutator_mem H h1 a c⟩
  have he : (⟨⁅a,b*c⁆,commutator_mem H h1 a (b*c)⟩ : H.level 2) =
      ⟨⁅a,b⁆,commutator_mem H h1 a b⟩ *
        ⟨b*u*b⁻¹,(level_normal H h0 2).conj_mem _ u.property b⟩ := by
    apply Subtype.ext
    simpa only [u,Subgroup.coe_mul,mul_assoc] using commutatorElement_mul_right_eq_mul_conj a b c
  dsimp only [pairing]
  rw [he,map_mul,map_mul,lower_conj H h0 h1 ξ]

lemma pairing_mul_left (a b c : G) :
    pairing H h0 h1 ξ (a*b) c = pairing H h0 h1 ξ a c * pairing H h0 h1 ξ b c := by
  let u : H.level 2 := ⟨⁅b,c⁆,commutator_mem H h1 b c⟩
  have he : (⟨⁅a*b,c⁆,commutator_mem H h1 (a*b) c⟩ : H.level 2) =
      ⟨a*u*a⁻¹,(level_normal H h0 2).conj_mem _ u.property a⟩ *
        ⟨⁅a,c⁆,commutator_mem H h1 a c⟩ := by
    apply Subtype.ext
    exact commutatorElement_mul_left_eq_conj_mul a b c
  dsimp only [pairing]
  rw [he,map_mul,map_mul,lower_conj H h0 h1 ξ,mul_comm]

 
def pairingHom (a : G) : G →* K where
  toFun := pairing H h0 h1 ξ a
  map_one' := by
    dsimp only [pairing]
    have he : (⟨⁅a,1⁆,commutator_mem H h1 a 1⟩ : H.level 2) = 1 := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [he,map_one,map_one]
  map_mul' := pairing_mul_right H h0 h1 ξ a

lemma pairing_self (a : G) : pairing H h0 h1 ξ a a = 1 := by
  dsimp only [pairing]
  have he : (⟨⁅a,a⁆,commutator_mem H h1 a a⟩ : H.level 2) = 1 := by
    apply Subtype.ext
    simp
  rw [he,map_one,map_one]

lemma pairing_swap (a b : G) : pairing H h0 h1 ξ b a = (pairing H h0 h1 ξ a b)⁻¹ := by
  have he : (⟨⁅b,a⁆,commutator_mem H h1 b a⟩ : H.level 2) =
      (⟨⁅a,b⁆,commutator_mem H h1 a b⟩ : H.level 2)⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def,mul_assoc]
  dsimp only [pairing]
  rw [he,map_inv,map_inv]

lemma diagonal_conj (a g : G) :
    ξ (diagonal H h0 h1 (a*g*a⁻¹)) = ξ (diagonal H h0 h1 g) := by
  simp only [map_mul,map_inv]
  calc
    _ = ξ (diagonal H h0 h1 g) * (ξ (diagonal H h0 h1 a) * (ξ (diagonal H h0 h1 a))⁻¹) := by ac_rfl
    _ = _ := by simp

lemma conjugate_lower (a b : G) (u : H.level 2) :
    ξ (restrictedConj H h0 h1 a b (lower H h0 u)) = ξ (lower H h0 u) := by
  have he : restrictedConj H h0 h1 a b (lower H h0 u) =
      lower H h0 ⟨b*u*b⁻¹,(level_normal H h0 2).conj_mem _ u.property b⟩ := by
    apply Subtype.ext
    change (a*1*a⁻¹,b*u*b⁻¹) = (1,b*u*b⁻¹)
    simp
  rw [he]
  exact lower_conj H h0 h1 ξ b u

lemma conjugate_diagonal (a b g : G) :
    ξ (restrictedConj H h0 h1 a b (diagonal H h0 h1 g)) =
      ξ (diagonal H h0 h1 g) * (pairing H h0 h1 ξ a g)⁻¹ * pairing H h0 h1 ξ b g := by
  let u : H.level 2 := (⟨⁅a,g⁆,commutator_mem H h1 a g⟩ : H.level 2)⁻¹ *
    ⟨⁅b,g⁆,commutator_mem H h1 b g⟩
  have ht : tail H h0 (restrictedConj H h0 h1 a b (diagonal H h0 h1 g)) =
      ⟨g⁻¹*u*g⁻¹⁻¹,(level_normal H h0 2).conj_mem _ u.property g⁻¹⟩ := by
    apply Subtype.ext
    change (a*g*a⁻¹)⁻¹ * (b*g*b⁻¹) = g⁻¹*(⁅a,g⁆⁻¹*⁅b,g⁆)*g⁻¹⁻¹
    simp [commutatorElement_def,mul_assoc]
  rw [character_split H h0 h1 ξ,ht]
  change ξ (diagonal H h0 h1 (a*g*a⁻¹)) * ξ (lower H h0 _) = _
  rw [diagonal_conj H h0 h1 ξ,lower_conj H h0 h1 ξ]
  simp only [u,map_mul,map_inv,pairing,mul_assoc]

 

theorem conjugate_character (a b : G) (x : level H h0 1) :
    ξ (restrictedConj H h0 h1 a b x) =
      ξ x * (pairing H h0 h1 ξ a x.val.1)⁻¹ * pairing H h0 h1 ξ b x.val.1 := by
  conv_lhs => rw [← split H h0 h1 x]
  simp only [map_mul,conjugate_diagonal H h0 h1 ξ,conjugate_lower H h0 h1 ξ]
  rw [character_split H h0 h1 ξ x]
  simp only [MonoidHom.comp_apply]
  ac_rfl

 

theorem character_lattice_iff (Γ : Subgroup G) (B : Subgroup K) :
    (∀ x : level H h0 1, x.val ∈ Γ.prod Γ → ξ x ∈ B) ↔
      (∀ g ∈ Γ, ξ (diagonal H h0 h1 g) ∈ B) ∧
      (∀ u : H.level 2, (u : G) ∈ Γ → ξ (lower H h0 u) ∈ B) := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h _ ⟨hg,hg⟩
    · intro u hu
      exact h _ ⟨Γ.one_mem,hu⟩
  · rintro ⟨hd,hl⟩ x hx
    rw [character_split H h0 h1 ξ]
    exact B.mul_mem (hd x.val.1 hx.1)
      (hl (tail H h0 x) (Γ.mul_mem (Γ.inv_mem hx.1) hx.2))

lemma pairing_lattice (Γ : Subgroup G) (B : Subgroup K)
    (hξ : ∀ x : level H h0 1, x.val ∈ Γ.prod Γ → ξ x ∈ B)
    {a b : G} (ha : a ∈ Γ) (hb : b ∈ Γ) : pairing H h0 h1 ξ a b ∈ B := by
  apply ((character_lattice_iff H h0 h1 ξ Γ B).mp hξ).2
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)) (Γ.inv_mem hb)

section Topology
variable [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace K] [IsTopologicalGroup K]

omit [IsTopologicalGroup G] in
lemma continuous_diagonal : Continuous (diagonal H h0 h1) := by
  apply Continuous.subtype_mk
  exact continuous_id.prodMk continuous_id

omit h1 [IsTopologicalGroup G] in
lemma continuous_lower : Continuous (lower H h0) := by
  apply Continuous.subtype_mk
  exact continuous_const.prodMk continuous_subtype_val

omit [IsTopologicalGroup K] in
lemma continuous_pairing (hξ : Continuous ξ) :
    Continuous (fun p : G × G => pairing H h0 h1 ξ p.1 p.2) := by
  apply hξ.comp
  apply (continuous_lower H h0).comp
  apply Continuous.subtype_mk
  simp only [commutatorElement_def]
  fun_prop
end Topology

end SquareHorizontalCharacter

end
end
end
end

end OAI
