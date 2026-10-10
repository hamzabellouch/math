import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareHorizontal01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement
end
 

 
section

 

namespace IntegralBilinear
open scoped BigOperators
noncomputable section
variable {d : ℕ}
abbrev V (d : ℕ) := Fin d → ℝ

def basisVector (i : Fin d) : V d := Pi.single i 1

lemma basis_expansion (x : V d) : x = ∑ i, x i • basisVector i := by
  classical
  ext j
  simp [basisVector,Finset.sum_apply,Pi.single_apply]

def leftHom (B : V d →+ (V d →+ ℝ)) (y : V d) : V d →+ ℝ where
  toFun x := B x y
  map_zero' := by simp
  map_add' x z := by simp

lemma continuous_left (B : V d →+ (V d →+ ℝ))
    (hB : Continuous (fun p : V d × V d => B p.1 p.2)) (y : V d) :
    Continuous (leftHom B y) := hB.comp (continuous_id.prodMk continuous_const)

lemma continuous_right (B : V d →+ (V d →+ ℝ))
    (hB : Continuous (fun p : V d × V d => B p.1 p.2)) (x : V d) :
    Continuous (B x) := hB.comp (continuous_const.prodMk continuous_id)

lemma coordinate_expansion (B : V d →+ (V d →+ ℝ))
    (hB : Continuous (fun p : V d × V d => B p.1 p.2)) (x y : V d) :
    B x y = ∑ i, ∑ j, x i * B (basisVector i) (basisVector j) * y j := by
  classical
  have left : B x y = ∑ i, x i * B (basisVector i) y := by
    change leftHom B y x = _
    conv_lhs => rw [basis_expansion x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_real_smul _ (continuous_left B hB y)]
    rfl
  rw [left]
  apply Finset.sum_congr rfl
  intro i _
  have right : B (basisVector i) y = ∑ j, y j * B (basisVector i) (basisVector j) := by
    conv_lhs => rw [basis_expansion y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_real_smul _ (continuous_right B hB (basisVector i))]
    rfl
  rw [right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

 

theorem integer_matrix (B : V d →+ (V d →+ ℝ))
    (hB : Continuous (fun p : V d × V d => B p.1 p.2))
    (hZ : ∀ u v : Fin d → ℤ, ∃ m : ℤ, B (fun i => u i) (fun i => v i) = m) :
    ∃ M : Matrix (Fin d) (Fin d) ℤ,
      ∀ x y : V d, B x y = ∑ i, ∑ j, x i * (M i j:ℝ) * y j := by
  classical
  have he (i j : Fin d) : ∃ m : ℤ, B (basisVector i) (basisVector j) = m := by
    obtain ⟨m,hm⟩ := hZ (Pi.single i 1) (Pi.single j 1)
    refine ⟨m,?_⟩
    have hsingle (v : Fin d) : (fun k => ((Pi.single v 1 : Fin d → ℤ) k : ℝ)) =
        basisVector v := by
      ext k
      simp [basisVector,Pi.single_apply]
    rw [hsingle,hsingle] at hm
    exact hm
  choose M hM using he
  refine ⟨M,?_⟩
  intro x y
  rw [coordinate_expansion B hB]
  simp_rw [hM]

theorem alternating_integer_matrix (B : V d →+ (V d →+ ℝ))
    (hB : Continuous (fun p : V d × V d => B p.1 p.2))
    (hZ : ∀ u v : Fin d → ℤ, ∃ m : ℤ, B (fun i => u i) (fun i => v i) = m)
    (halt : ∀ x, B x x = 0) :
    ∃ M : Matrix (Fin d) (Fin d) ℤ,
      (∀ i, M i i = 0) ∧ (∀ i j, M j i = -(M i j)) ∧
      ∀ x y : V d, B x y = ∑ i, ∑ j, x i * (M i j:ℝ) * y j := by
  classical
  obtain ⟨M,hM⟩ := integer_matrix B hB hZ
  have hentry (i j : Fin d) : B (basisVector i) (basisVector j) = (M i j:ℝ) := by
    rw [hM]
    simp [basisVector,Pi.single_apply]
  refine ⟨M,?_,?_,hM⟩
  · intro i
    have hi := halt (basisVector i)
    rw [hentry] at hi
    exact_mod_cast hi
  · intro i j
    have h := halt (basisVector i + basisVector j)
    simp only [map_add,AddMonoidHom.add_apply] at h
    rw [halt,halt,zero_add,add_zero,hentry,hentry] at h
    exact_mod_cast (show (M j i:ℝ) = -(M i j:ℝ) by linarith)

 
def contraction (M : Matrix (Fin d) (Fin d) ℤ) (x : V d) : V d :=
  fun j => ∑ i, x i*(M i j:ℝ)

lemma contraction_pairing (M : Matrix (Fin d) (Fin d) ℤ) (x y : V d) :
    (∑ i, ∑ j, x i*(M i j:ℝ)*y j) = ∑ j, contraction M x j*y j := by
  simp only [contraction,Finset.sum_mul]
  exact Finset.sum_comm

lemma contraction_add (M : Matrix (Fin d) (Fin d) ℤ) (x y : V d) :
    contraction M (x+y) = contraction M x+contraction M y := by
  ext j
  simp [contraction,add_mul,Finset.sum_add_distrib]

lemma contraction_integer (M : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ) (j : Fin d) :
    contraction M (fun i => x i) j = ((∑ i, x i*M i j : ℤ):ℝ) := by
  simp [contraction]

 

lemma lattice_correction (M : Matrix (Fin d) (Fin d) ℤ) (x : V d)
    (u : Fin d → ℤ) :
    contraction M (x + fun i => (u i:ℝ)) =
      contraction M x + fun j => ((∑ i, u i*M i j:ℤ):ℝ) := by
  rw [contraction_add]
  congr 1
  ext j
  exact contraction_integer M u j

end
end IntegralBilinear
end
 

 
section

open scoped BigOperators commutatorElement
noncomputable section
namespace MalcevHorizontal
open RationalLattice CubeFaces LeibmanSquare SquareHorizontalCharacter
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)

 
def horizontal (g : G) : Fin d → ℝ := fun i => c.coord g (Fin.castLE hd i)

 

def coordSection (_hd : d ≤ n) (x : Fin d → ℝ) : G :=
  c.coord.symm (fun i => if h : i.val < d then x ⟨i.val,h⟩ else 0)

lemma horizontal_one : horizontal c hd 1 = 0 := by
  ext i
  exact c.one_coord _

lemma continuous_horizontal : Continuous (horizontal c hd) := by
  exact continuous_pi (fun i => (continuous_apply _).comp c.coord.continuous)

lemma continuous_section : Continuous (coordSection c hd) := by
  apply c.coord.symm.continuous.comp
  apply continuous_pi
  intro i
  by_cases h : i.val < d
  · simpa only [h, dite_true] using (continuous_apply (⟨i.val,h⟩ : Fin d))
  · simpa only [h, dite_false] using (continuous_const : Continuous (fun _ : Fin d → ℝ => (0 : ℝ)))

@[simp] lemma horizontal_section (x : Fin d → ℝ) :
    horizontal c hd (coordSection c hd x) = x := by
  ext i
  simp [horizontal, coordSection, i.isLt]

@[simp] lemma section_zero : coordSection c hd 0 = 1 := by
  apply c.coord.injective
  ext i
  simp [coordSection, c.one_coord]

variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i) = 0)
include hlin

lemma horizontal_mul (a b : G) :
    horizontal c hd (a*b) = horizontal c hd a + horizontal c hd b := by
  ext i
  simp only [horizontal, c.mul_coord, hlin, MvPolynomial.eval₂_zero, add_zero, Pi.add_apply]

lemma horizontal_inv (a : G) : horizontal c hd a⁻¹ = - horizontal c hd a := by
  have h := horizontal_mul c hd hlin a a⁻¹
  rw [mul_inv_cancel, horizontal_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

 
def quotientHom : G →* Multiplicative (Fin d → ℝ) where
  toFun g := Multiplicative.ofAdd (horizontal c hd g)
  map_one' := horizontal_one c hd
  map_mul' := horizontal_mul c hd hlin

lemma continuous_quotientHom : Continuous (quotientHom c hd hlin) :=
  continuous_horizontal c hd

variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable (hlevel : ∀ g : G, g ∈ H.level 2 ↔ horizontal c hd g = 0)
variable (ξ : level H h0 1 →* Multiplicative ℝ)
include hlevel

lemma pairing_eq_right {a b e : G} (he : horizontal c hd b = horizontal c hd e) :
    pairing H h0 h1 ξ a b = pairing H h0 h1 ξ a e := by
  have hb : b*e⁻¹ ∈ H.level 2 := by
    rw [hlevel, horizontal_mul c hd hlin, horizontal_inv c hd hlin, he, add_neg_cancel]
  have hz := lower_commutator H h0 h1 ξ a ⟨b*e⁻¹,hb⟩
  change pairing H h0 h1 ξ a (b*e⁻¹) = 1 at hz
  change (pairingHom H h0 h1 ξ a) (b*e⁻¹) = 1 at hz
  rw [map_mul, map_inv] at hz
  exact mul_inv_eq_one.mp hz

lemma pairing_eq_left {a b e : G} (he : horizontal c hd a = horizontal c hd b) :
    pairing H h0 h1 ξ a e = pairing H h0 h1 ξ b e := by
  rw [pairing_swap H h0 h1 ξ e a, pairing_swap H h0 h1 ξ e b]
  rw [pairing_eq_right c hd hlin H h0 h1 hlevel ξ he]

lemma pairing_projection (a b : G) :
    pairing H h0 h1 ξ a b = pairing H h0 h1 ξ
      (coordSection c hd (horizontal c hd a)) (coordSection c hd (horizontal c hd b)) := by
  rw [pairing_eq_left c hd hlin H h0 h1 hlevel ξ (horizontal_section c hd _).symm]
  exact pairing_eq_right c hd hlin H h0 h1 hlevel ξ (horizontal_section c hd _).symm

lemma section_add_pairing_left (x y z : Fin d → ℝ) :
    pairing H h0 h1 ξ (coordSection c hd (x+y)) (coordSection c hd z) =
      pairing H h0 h1 ξ (coordSection c hd x) (coordSection c hd z) *
      pairing H h0 h1 ξ (coordSection c hd y) (coordSection c hd z) := by
  rw [pairing_eq_left c hd hlin H h0 h1 hlevel ξ (show
    horizontal c hd (coordSection c hd (x+y)) =
      horizontal c hd (coordSection c hd x * coordSection c hd y) by
      simp [horizontal_mul c hd hlin])]
  exact pairing_mul_left H h0 h1 ξ _ _ _

lemma section_add_pairing_right (x y z : Fin d → ℝ) :
    pairing H h0 h1 ξ (coordSection c hd x) (coordSection c hd (y+z)) =
      pairing H h0 h1 ξ (coordSection c hd x) (coordSection c hd y) *
      pairing H h0 h1 ξ (coordSection c hd x) (coordSection c hd z) := by
  rw [pairing_eq_right c hd hlin H h0 h1 hlevel ξ (show
    horizontal c hd (coordSection c hd (y+z)) =
      horizontal c hd (coordSection c hd y * coordSection c hd z) by
      simp [horizontal_mul c hd hlin])]
  exact pairing_mul_right H h0 h1 ξ _ _ _

 

def bilinear : (Fin d → ℝ) →+ ((Fin d → ℝ) →+ ℝ) where
  toFun x := {
    toFun y := Multiplicative.toAdd (pairing H h0 h1 ξ (coordSection c hd x) (coordSection c hd y))
    map_zero' := by
      simp only [section_zero]
      exact congrArg Multiplicative.toAdd (map_one (pairingHom H h0 h1 ξ _))
    map_add' y z := congrArg Multiplicative.toAdd
      (section_add_pairing_right c hd hlin H h0 h1 hlevel ξ x y z) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change Multiplicative.toAdd (pairing H h0 h1 ξ (coordSection c hd 0) (coordSection c hd y)) = 0
    rw [section_zero, pairing_swap H h0 h1 ξ (coordSection c hd y) 1]
    change Multiplicative.toAdd ((pairingHom H h0 h1 ξ (coordSection c hd y)) 1)⁻¹ = 0
    simp
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    exact congrArg Multiplicative.toAdd
      (section_add_pairing_left c hd hlin H h0 h1 hlevel ξ x y z)

section
variable [IsTopologicalGroup G]

lemma bilinear_continuous (hξ : Continuous ξ) :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      bilinear c hd hlin H h0 h1 hlevel ξ p.1 p.2) := by
  exact (continuous_pairing H h0 h1 ξ hξ).comp
    ((continuous_section c hd).comp continuous_fst |>.prodMk
      ((continuous_section c hd).comp continuous_snd))

end

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)

omit hlin hlevel in
include hΓ in
lemma integer_section (z : Fin d → ℤ) : coordSection c hd (fun i => (z i : ℝ)) ∈ Γ := by
  rw [hΓ]
  intro i
  by_cases h : i.val < d
  · exact ⟨z ⟨i.val,h⟩, by simp [coordSection,h]⟩
  · exact ⟨0, by simp [coordSection,h]⟩

include hΓ

 

lemma bilinear_integer
    (hξΓ : ∀ x : level H h0 1, x.val ∈ Γ.prod Γ → ∃ z : ℤ,
      Multiplicative.toAdd (ξ x) = z) (u v : Fin d → ℤ) :
    ∃ z : ℤ, bilinear c hd hlin H h0 h1 hlevel ξ
      (fun i => (u i : ℝ)) (fun i => (v i : ℝ)) = z := by
  apply hξΓ
  constructor
  · exact Γ.one_mem
  · exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem
      (integer_section c hd Γ hΓ u) (integer_section c hd Γ hΓ v))
      (Γ.inv_mem (integer_section c hd Γ hΓ u)))
      (Γ.inv_mem (integer_section c hd Γ hΓ v))

 

variable [IsTopologicalGroup G]

theorem square_integer_matrix (hξ : Continuous ξ)
    (hξΓ : ∀ x : level H h0 1, x.val ∈ Γ.prod Γ → ∃ z : ℤ,
      Multiplicative.toAdd (ξ x) = z) :
    ∃ M : Matrix (Fin d) (Fin d) ℤ,
      (∀ i, M i i = 0) ∧ (∀ i j, M j i = - M i j) ∧
      ∀ a b : G, Multiplicative.toAdd (pairing H h0 h1 ξ a b) =
        ∑ i, ∑ j, horizontal c hd a i * (M i j : ℝ) * horizontal c hd b j := by
  obtain ⟨M,hdiag,halt,hM⟩ := IntegralBilinear.alternating_integer_matrix
    (bilinear c hd hlin H h0 h1 hlevel ξ)
    (bilinear_continuous c hd hlin H h0 h1 hlevel ξ hξ)
    (bilinear_integer c hd hlin H h0 h1 hlevel ξ Γ hΓ hξΓ)
    (fun x => congrArg Multiplicative.toAdd (pairing_self H h0 h1 ξ (coordSection c hd x)))
  refine ⟨M,hdiag,halt,fun a b => ?_⟩
  rw [pairing_projection c hd hlin H h0 h1 hlevel ξ a b]
  exact hM _ _

end MalcevHorizontal

end
end
end
end
end

end OAI
