import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevTail01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators
noncomputable section
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevTailFactor
open RationalLattice MalcevCharacters MalcevTailSection IntegerHyperplane
open CubeFaces CubePolynomials RationalFactorPeriods
variable {G : Type*} [Group G] [TopologicalSpace G] {n l : ℕ}
variable (c : RealCoordinates G n) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (k : Fin n → ℤ)
variable (hχ : ∀ g, (χ g).toAdd = form k (c.coord g))
variable (r : Fin l → ℕ) (a : Fin l → G)

def beta (i : Fin l) : ℝ := (χ (a i)).toAdd

def numerator (i : Fin l) : ℤ := round (beta χ a i)

def error (i : Fin l) : ℝ := beta χ a i - (numerator χ a i : ℝ)

def smallCoeff (i : Fin l) : G := tailSection c k (r i) (error χ a i)

def rationalGenerator (i : Fin l) : G := tailSection c k (r i) 1

def rationalCoeff (i : Fin l) : G := rationalGenerator c k r i ^ numerator χ a i

variable (ha : ∀ i, ∀ u : Fin n, u.val < r i → c.coord (a i) u = 0)
include hχ ha in
lemma beta_zero (i : Fin l) (h : ¬ HasPivot k (r i)) : beta χ a i = 0 := by
  rw [beta,hχ]
  exact form_zero_of_no_pivot k (r i) h _ (ha i)

include hχ ha in
lemma error_zero (i : Fin l) (h : ¬ HasPivot k (r i)) : error χ a i = 0 := by
  simp [error,numerator,beta_zero c χ k hχ r a ha i h]

include hsk in
lemma rationalCoeff_eq (i : Fin l) : rationalCoeff c χ k r a i =
    tailSection c k (r i) (numerator χ a i) := by
  simpa [rationalCoeff,rationalGenerator] using
    (section_zpow c hsk k (r i) 1 (numerator χ a i)).symm

include hχ ha in
lemma small_character (i : Fin l) :
    (χ (smallCoeff c χ k r a i)).toAdd = error χ a i := by
  exact character_section c χ k hχ (r i) (error χ a i)
    (error_zero c χ k hχ r a ha i)

include hsk hχ ha in
lemma rational_character (i : Fin l) :
    (χ (rationalCoeff c χ k r a i)).toAdd = numerator χ a i := by
  rw [rationalCoeff_eq c hsk χ k r a i]
  apply character_section c χ k hχ
  intro h
  simp [numerator,beta_zero c χ k hχ r a ha i h]

lemma generator_rational (i : Fin l) : IsRational c (rationalGenerator c k r i) := by
  simpa [rationalGenerator] using section_rational c k (r i) 1

lemma small_bound (i : Fin l) (u : Fin n) :
    |c.coord (smallCoeff c χ k r a i) u| ≤ ‖(beta χ a i : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  exact section_bound c k (r i) (error χ a i) u

variable (j : Fin l → ℕ)
include hsk hχ ha in
lemma word_character_split (b : ℤ) :
    (χ (orderedWord a j b)).toAdd =
      (χ (orderedWord (smallCoeff c χ k r a) j b)).toAdd +
      (χ (orderedWord (rationalCoeff c χ k r a) j b)).toAdd := by
  simp only [orderedWord_character,small_character c χ k hχ r a ha,
    rational_character c hsk χ k hχ r a ha,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ((Ring.choose b (j i) : ℤ) : ℝ)*beta χ a i = _
  simp [error,mul_sub]

include hsk hχ ha in
lemma residual_kernel (b : ℤ) :
    (orderedWord (smallCoeff c χ k r a) j b)⁻¹ * orderedWord a j b *
      (orderedWord (rationalCoeff c χ k r a) j b)⁻¹ ∈ χ.ker := by
  change χ _ = 1
  apply Multiplicative.toAdd.injective
  simp only [map_mul,map_inv,toAdd_mul,toAdd_inv,
    toAdd_one]
  linarith [word_character_split c hsk χ k hχ r a ha j b]

variable (H : Filtration G) (q : ℕ)
variable (hlevel : ∀ i g, g ∈ H.level (j i+q) ↔ ∀ u : Fin n, u.val < r i → c.coord g u = 0)
include hlevel in
lemma small_polynomial : orderedWord (smallCoeff c χ k r a) j ∈ polynomials H q := by
  apply orderedWord_mem
  intro i
  rw [hlevel]
  exact section_tail c k (r i) _

include hsk hlevel in
lemma rational_polynomial : orderedWord (rationalCoeff c χ k r a) j ∈ polynomials H q := by
  apply orderedWord_mem
  intro i
  rw [rationalCoeff_eq c hsk χ k r a i,hlevel]
  exact section_tail c k (r i) _

end MalcevTailFactor
end
end
 

 
section
open scoped commutatorElement
noncomputable section
namespace CubePolynomials
open CubeFaces
variable {G A : Type*} [Group G] [Group A]

 

theorem residual_refinement (H : Filtration G) (s : ℕ) (hbot : H.level s = ⊥)
    (φ : A →* G) (χ : A →* Multiplicative ℝ)
    (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ χ.ker.map φ)
    (g : ℤ → G) (hg : g ∈ polynomials H 0) (a : G) (ha : a ∈ H.level 1)
    (q e v : ℤ → A) (he : (fun n => φ (e n)) ∈ polynomials H 0)
    (hv : (fun n => φ (v n)) ∈ polynomials H 0)
    (hgq : ∀ n, g n = φ (q n) * a^n)
    (hker : ∀ n, (e n)⁻¹ * q n * (v n)⁻¹ ∈ χ.ker) :
    (fun n => (φ (e n))⁻¹ * g n * (φ (v n))⁻¹) ∈
      polynomials (H.refine (χ.ker.map φ) hcomm) 0 := by
  let K := χ.ker.map φ
  have hf : (fun n => (φ (e n))⁻¹ * g n * (φ (v n))⁻¹) ∈ polynomials H 0 :=
    (polynomials H 0).mul_mem ((polynomials H 0).mul_mem
      ((polynomials H 0).inv_mem he) hg) ((polynomials H 0).inv_mem hv)
  apply refine_of_linear_coset H _ hcomm s hbot _ hf a ha
  intro n
  have hrow : (φ (e n))⁻¹ * φ (q n) * (φ (v n))⁻¹ ∈ K := by
    have hm : φ ((e n)⁻¹ * q n * (v n)⁻¹) ∈ K :=
      Subgroup.mem_map_of_mem φ (hker n)
    simpa only [map_mul,map_inv] using hm
  have hc := hcomm (φ (v n)) (a^n)
  have hprod := K.mul_mem hrow hc
  convert hprod using 1
  rw [hgq]
  simp only [commutatorElement_def]
  group

end CubePolynomials
end
end
 

 
section
noncomputable section
namespace RationalFactorPeriods
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [PreconnectedSpace G] [LocallyCompactSpace G] [T2Space G] {n l : ℕ}

 

theorem uniform_rational_word_period
    (c : RationalLattice.RealCoordinates G n) (Γ : Subgroup G) [DiscreteTopology Γ]
    (hΓrat : Γ ≤ RationalLattice.rationalSubgroup c)
    (C : Set G) (hC : IsCompact C) (hreps : ∀ g : G, ∃ x ∈ C, x⁻¹*g ∈ Γ)
    (v : Fin l → G) (hv : ∀ i, RationalLattice.IsRational c (v i))
    (j : Fin l → ℕ) (s : ℕ) (hj : ∀ i, j i ≤ s) :
    ∃ T : ℕ, 0 < T ∧ ∀ m : Fin l → ℤ,
      Function.Periodic (fun b => (QuotientGroup.mk
        (orderedWord (fun i => v i ^ m i) j b) : G ⧸ Γ)) (T : ℤ) := by
  classical
  let S := Finset.univ.image v
  have hSrat : ∀ g ∈ S, RationalLattice.IsRational c g := by
    intro g hg
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hg
    exact hv i
  obtain ⟨H,hΓH,hSH,hHrat,hHd,hHi⟩ :=
    RationalLattice.finite_rational_extension c Γ hΓrat C hC hreps S hSrat
  let : (Γ.subgroupOf H).FiniteIndex := hHi
  let : Fintype (H ⧸ Γ.subgroupOf H) := Fintype.ofFinite _
  let K := Equiv.Perm (H ⧸ Γ.subgroupOf H)
  let φ : H →* K := MulAction.toPermHom H (H ⧸ Γ.subgroupOf H)
  have hvH (i : Fin l) : v i ∈ H := hSH (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  refine ⟨Fintype.card K * s.factorial,Nat.mul_pos Fintype.card_pos s.factorial_pos,?_⟩
  intro m b
  let a : Fin l → H := fun i => ⟨v i ^ m i,H.zpow_mem (hvH i) _⟩
  have he := congrArg (fun e : K => e (QuotientGroup.mk (1:H)))
    (finite_image_periodic φ a j s hj b)
  have hquot : (QuotientGroup.mk (orderedWord a j (b+(Fintype.card K*s.factorial:ℕ))) : H ⧸ Γ.subgroupOf H) =
      QuotientGroup.mk (orderedWord a j b) := by
    simpa [φ,K,MulAction.toPermHom] using he
  have hmem := QuotientGroup.eq.mp hquot
  have heG : (QuotientGroup.mk ((orderedWord a j (b+(Fintype.card K*s.factorial:ℕ)) : H):G) : G ⧸ Γ) =
      QuotientGroup.mk ((orderedWord a j b : H):G) := QuotientGroup.eq.mpr hmem
  have hmap (b : ℤ) : ((orderedWord a j b : H):G) =
      orderedWord (fun i => v i ^ m i) j b := orderedWord_map H.subtype a j b
  simpa only [hmap] using heG

end RationalFactorPeriods
end
end
 

 
section
open scoped commutatorElement BigOperators
noncomputable section
namespace CharacterFactorization
open CubeFaces CubePolynomials RationalFactorPeriods RationalLattice MalcevCharacters MalcevTailFactor
variable {G : Type*} [Group G] [TopologicalSpace G]
variable (H : Filtration G) {n s : ℕ} (c : RealCoordinates (H.level 2) n) (hsk : SecondKind c)
variable (χ : H.level 2 →* Multiplicative ℝ) (k : Fin n → ℤ)
variable (hχ : ∀ x, (χ x).toAdd = IntegerHyperplane.form k (c.coord x))
variable (r : Fin s → ℕ)
variable (hlevel : ∀ i (x : H.level 2), x.val ∈ H.level (i.val+2) ↔
  ∀ u : Fin n, u.val < r i → c.coord x u = 0)
variable (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ χ.ker.map (H.level 2).subtype)

def epsilon (a : Fin s → H.level 2) (z : ℤ) : G :=
  (orderedWord (smallCoeff c χ k r a) (fun i => i.val+2) z).val

def gamma (a : Fin s → H.level 2) (z : ℤ) : G :=
  (orderedWord (rationalCoeff c χ k r a) (fun i => i.val+2) z).val

def residual (g : ℤ → G) (a : Fin s → H.level 2) (z : ℤ) : G :=
  (epsilon H c χ k r a z)⁻¹ * g z * (gamma H c χ k r a z)⁻¹

lemma factorization_identity (g : ℤ → G) (a : Fin s → H.level 2) (z : ℤ) :
    g z = epsilon H c χ k r a z * residual H c χ k r g a z * gamma H c χ k r a z := by
  unfold residual
  group

include hlevel in
lemma epsilon_polynomial (a : Fin s → H.level 2) :
    epsilon H c χ k r a ∈ polynomials H 0 := by
  have he : epsilon H c χ k r a = orderedWord (fun i => (smallCoeff c χ k r a i).val)
      (fun i => i.val+2) := funext (fun z => orderedWord_map (H.level 2).subtype _ _ z)
  rw [he]
  apply orderedWord_mem
  intro i
  simp only [add_zero]
  rw [hlevel]
  exact MalcevTailSection.section_tail c k (r i) _

include hsk hlevel in
lemma gamma_polynomial (a : Fin s → H.level 2) :
    gamma H c χ k r a ∈ polynomials H 0 := by
  have he : gamma H c χ k r a = orderedWord (fun i => (rationalCoeff c χ k r a i).val)
      (fun i => i.val+2) := funext (fun z => orderedWord_map (H.level 2).subtype _ _ z)
  rw [he]
  apply orderedWord_mem
  intro i
  simp only [add_zero]
  rw [hlevel,rationalCoeff_eq c hsk χ k r a i]
  exact MalcevTailSection.section_tail c k (r i) _

lemma epsilon_zero (a : Fin s → H.level 2) : epsilon H c χ k r a 0 = 1 := by
  have he : ∀ i : Fin s, smallCoeff c χ k r a i ^ Ring.choose (0:ℤ) (i.val+2) = 1 := by
    intro i
    rw [Ring.choose_zero_pos ℤ (by omega),zpow_zero]
  simp [epsilon,orderedWord]

include hsk hχ hlevel in
lemma residual_polynomial (hbot : H.level s = ⊥)
    (g : ℤ → G) (hg : g ∈ polynomials H 0) (h1 : g 1 ∈ H.level 1)
    (a : Fin s → H.level 2) (ha : ∀ i, (a i).val ∈ H.level (i.val+2))
    (he : ∀ z, g z = (orderedWord a (fun i => i.val+2) z).val * g 1 ^ z) :
    residual H c χ k r g a ∈ polynomials (H.refine (χ.ker.map (H.level 2).subtype) hcomm) 0 := by
  apply residual_refinement H s hbot (H.level 2).subtype χ hcomm g hg (g 1) h1
    (orderedWord a (fun i => i.val+2))
    (orderedWord (smallCoeff c χ k r a) (fun i => i.val+2))
    (orderedWord (rationalCoeff c χ k r a) (fun i => i.val+2))
    (epsilon_polynomial H c χ k r hlevel a)
    (gamma_polynomial H c hsk χ k r hlevel a) he
  exact MalcevTailFactor.residual_kernel c hsk χ k hχ r a
    (fun i => (hlevel i (a i)).mp (ha i)) (fun i => i.val+2)

include hsk hχ hlevel in
 

theorem normalized_factorization (hbot : H.level s = ⊥)
    (g : ℤ → G) (hg : g ∈ polynomials H 0) (h0 : g 0=1) (h1 : g 1 ∈ H.level 1) :
    ∃ a : Fin s → H.level 2,
      (∀ i, (a i).val ∈ H.level (i.val+2)) ∧
      (∀ z, g z = (orderedWord a (fun i => i.val+2) z).val * g 1 ^ z) ∧
      epsilon H c χ k r a ∈ polynomials H 0 ∧
      gamma H c χ k r a ∈ polynomials H 0 ∧
      residual H c χ k r g a ∈ polynomials (H.refine (χ.ker.map (H.level 2).subtype) hcomm) 0 := by
  obtain ⟨a,ha,he⟩ := NilpotentTaylor.normalized_subgroup_taylor H s hbot g hg h0 h1
  exact ⟨a,ha,he,epsilon_polynomial H c χ k r hlevel a,
    gamma_polynomial H c hsk χ k r hlevel a,
    residual_polynomial H c hsk χ k hχ r hlevel hcomm hbot g hg h1 a ha he⟩

 

variable [IsTopologicalGroup G] [T2Space G]

theorem uniform_gamma_period (Γ : Subgroup G)
    (hΓ : ∀ x : H.level 2, x.val ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord x i = z) :
    ∃ T : ℕ, 0 < T ∧ ∀ a : Fin s → H.level 2,
      Function.Periodic (fun z => (QuotientGroup.mk (gamma H c χ k r a z) : G ⧸ Γ)) (T:ℤ) := by
  let L := Γ.comap (H.level 2).subtype
  have hL : ∀ x : H.level 2, x ∈ L ↔ ∀ i, ∃ z : ℤ, c.coord x i = z := hΓ
  let : DiscreteTopology L := integerCoordinates_discrete c L hL
  let : ConnectedSpace (H.level 2) := c.coord.symm.surjective.connectedSpace c.coord.symm.continuous
  let : LocallyCompactSpace (H.level 2) := c.coord.locallyCompactSpace_iff.mpr inferInstance
  obtain ⟨C,hC,hrep⟩ := compact_reps_of_integerCoordinates c L hL
  obtain ⟨T,hT,hper⟩ := uniform_rational_word_period c L (integerCoordinates_rational c L hL)
    C hC hrep (rationalGenerator c k r) (generator_rational c k r)
    (fun i => i.val+2) (s+2) (fun i => by omega)
  refine ⟨T,hT,fun a z => ?_⟩
  have hp := hper (numerator χ a) z
  have hm := QuotientGroup.eq.mp hp
  exact QuotientGroup.eq.mpr hm

end CharacterFactorization

end
end
end
end
end

end OAI
