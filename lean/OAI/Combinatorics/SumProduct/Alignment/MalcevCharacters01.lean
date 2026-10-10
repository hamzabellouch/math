import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice08
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
noncomputable section
open scoped BigOperators
namespace RationalLattice
variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
variable {m n : ℕ} (c : RealCoordinates G m) (d : RealCoordinates K n)
variable (F : K →* G)
variable (hpoly : ∀ i, RationalPolynomialMap.IsPolynomial (fun x : Fin n → ℝ => c.coord (F (d.coord.symm x)) i))

include hpoly in
 

theorem rationalHom_origin_grid : ∃ E : ℕ, 0 < E ∧ ∀ x : Fin n → ℝ,
    (∀ j, ∃ z : ℤ, x j = (E:ℝ)*(z:ℝ)) →
    ∀ i, ∃ z : ℤ, c.coord (F (d.coord.symm x)) i = z := by
  classical
  choose P hP using hpoly
  choose D hD hgrid using (fun i => TriangularDenominators.polynomial_origin_grid_real (P i))
  let E := ∏ i, D i
  have hE : 0 < E := Finset.prod_pos (fun i _ => hD i)
  refine ⟨E,hE,?_⟩
  intro x hx i
  have hDi : D i ∣ E := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  have hzero : d.coord.symm (fun _ => 0) = 1 := by
    apply d.coord.injective
    funext j
    rw [Homeomorph.apply_symm_apply,d.one_coord]
  have hP0 : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun _ => 0) (P i) = 0 := by
    rw [← hP i]
    change c.coord (F (d.coord.symm (fun _ => 0))) i = 0
    rw [hzero,map_one,c.one_coord]
  obtain ⟨z,hz⟩ := hgrid i 1 x (by
    intro j
    obtain ⟨a,ha⟩ := hx j
    obtain ⟨b,hb⟩ := hDi
    refine ⟨(b:ℤ)*a,?_⟩
    rw [ha,hb]
    push_cast
    ring)
  refine ⟨z,?_⟩
  change ((fun x => c.coord (F (d.coord.symm x)) i) x) = (z:ℝ)
  rw [hP i]
  simpa only [hP0,sub_zero,Nat.cast_one,one_mul] using hz

variable [IsTopologicalGroup G] [IsTopologicalGroup K]
variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
variable (hc : Continuous F) (hinj : Function.Injective F)
include hpoly hΓ hc hinj in
 

theorem exists_integer_sublattice :
    ∃ Λ : Subgroup K, ∃ e : RealCoordinates K n,
      (∀ g : K, g ∈ Λ ↔ ∀ i, ∃ z : ℤ, e.coord g i = z) ∧
      Λ ≤ Γ.comap F ∧ (Λ.subgroupOf (Γ.comap F)).FiniteIndex ∧
      (∀ g : K, ∀ i, e.coord g i = 0 ↔ d.coord g i = 0) := by
  classical
  obtain ⟨E,hE,hgrid⟩ := rationalHom_origin_grid c d F hpoly
  obtain ⟨w,hpos,hEw,hw⟩ := exists_lattice_weights d E hE
  let Λ := weightedLattice d w hw
  let e := scaledCoordinates d w hpos
  have hΛ : ∀ g : K, g ∈ Λ ↔ ∀ i, ∃ z : ℤ, e.coord g i = z :=
    weightedLattice_iff d w hw hpos
  have hle : Λ ≤ Γ.comap F := by
    intro g hg
    apply (hΓ (F g)).mpr
    have hx : ∀ j, ∃ z : ℤ, d.coord g j = (E:ℝ)*(z:ℝ) := by
      intro j
      obtain ⟨a,ha⟩ := hg j
      obtain ⟨b,hb⟩ := hEw j
      refine ⟨(b:ℤ)*a,?_⟩
      rw [ha,hb]
      push_cast
      ring
    simpa using hgrid (d.coord g) hx
  let : T2Space K := d.coord.symm.t2Space
  let : DiscreteTopology Γ := integerCoordinates_discrete c Γ hΓ
  let : DiscreteTopology (Γ.comap F) :=
    DiscreteTopology.preimage_of_continuous_injective (Γ : Set G) hc hinj
  obtain ⟨C,hC,hrep⟩ := compact_reps_of_integerCoordinates e Λ hΛ
  have hi := TriangularDenominators.finiteIndex_of_compact_reps Λ (Γ.comap F) hle C hC hrep
  refine ⟨Λ,e,hΛ,hle,hi,?_⟩
  intro g i
  change d.coord g i/(w i:ℝ) = 0 ↔ d.coord g i = 0
  rw [div_eq_zero_iff]
  have hne : (w i:ℝ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  simp [hne]

end RationalLattice

namespace FiniteCoverCharacters
variable {G : Type*} [Group G]
variable (Λ Γ : Subgroup G) (hle : Λ ≤ Γ) [(Λ.subgroupOf Γ).FiniteIndex]

 

def denominator : ℕ := (Λ.subgroupOf Γ).index.factorial

omit [(Λ.subgroupOf Γ).FiniteIndex] in
lemma denominator_pos [(Λ.subgroupOf Γ).FiniteIndex] :
    0 < denominator Λ Γ := Nat.factorial_pos _

include hle in
lemma pow_denominator_mem (g : G) (hg : g ∈ Γ) : g^(denominator Λ Γ) ∈ Λ := by
  have he := (Λ.subgroupOf Γ).pow_mem_of_index_ne_zero_of_dvd
    (Subgroup.FiniteIndex.index_ne_zero) (⟨g,hg⟩ : Γ)
    (n:=denominator Λ Γ) (fun m hm hmi => Nat.dvd_factorial hm hmi)
  exact (Subgroup.subgroupOfEquivOfLe hle ⟨_,he⟩).property

include hle in
lemma integral_after_scaling (χ : G →* Multiplicative ℝ)
    (hz : ∀ g ∈ Λ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z) :
    ∀ g ∈ Γ, ∃ z : ℤ, (denominator Λ Γ:ℝ)*Multiplicative.toAdd (χ g) = z := by
  intro g hg
  obtain ⟨z,hz⟩ := hz _ (pow_denominator_mem Λ Γ hle g hg)
  refine ⟨z,?_⟩
  simpa only [map_pow,toAdd_pow,nsmul_eq_mul] using hz

end FiniteCoverCharacters

end
end
 

 
section
noncomputable section
open scoped BigOperators commutatorElement
namespace MalcevCharacters
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (N : Subgroup G) [N.Normal] (hcomm : _root_.commutator G ≤ N)

include hsk hcomm in
 

omit [IsTopologicalGroup G] in
lemma quotient_coord_add [IsTopologicalGroup G] (x y : Fin n → ℝ) :
    (QuotientGroup.mk (c.coord.symm (x+y)) : G ⧸ N) =
      QuotientGroup.mk (c.coord.symm x) * QuotientGroup.mk (c.coord.symm y) := by
  let : IsMulCommutative (G ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := mul_comm' }
  have he (v : Fin n → ℝ) : (QuotientGroup.mk (c.coord.symm v) : G ⧸ N) =
      (List.ofFn (fun i => QuotientGroup.mk (axis c i (v i)) : Fin n → G ⧸ N)).prod := by
    conv_lhs => rw [hsk.ordered (c.coord.symm v)]
    change (QuotientGroup.mk' N) (List.ofFn _ |>.prod) = _
    rw [map_list_prod,List.map_ofFn]
    simp only [Homeomorph.apply_symm_apply]
    rfl
  rw [he,he,he]
  simp_rw [Pi.add_apply,hsk.axis_add,QuotientGroup.mk_mul]
  simp only [List.prod_ofFn,Finset.prod_mul_distrib]

 

def quotientParameterHom : Multiplicative (Fin n → ℝ) →* G ⧸ N where
  toFun x := QuotientGroup.mk (c.coord.symm x.toAdd)
  map_one' := by
    have h0 : c.coord.symm (0 : Fin n → ℝ) = 1 := by
      apply c.coord.injective
      ext i
      simp only [Homeomorph.apply_symm_apply,Pi.zero_apply,c.one_coord]
    change QuotientGroup.mk (c.coord.symm 0) = 1
    rw [h0]
    rfl
  map_mul' x y := quotient_coord_add c hsk N hcomm x.toAdd y.toAdd

lemma quotientParameterHom_surjective : Function.Surjective (quotientParameterHom c hsk N hcomm) := by
  intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
  exact ⟨Multiplicative.ofAdd (c.coord g),by simp [quotientParameterHom]⟩

variable (k : Fin n → ℝ)
def linearParameterHom : Multiplicative (Fin n → ℝ) →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (∑ i, x.toAdd i * k i)
  map_one' := by apply Multiplicative.toAdd.injective; simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change (∑ i, (x.toAdd i+y.toAdd i)*k i) = _
    simp [add_mul,Finset.sum_add_distrib]

variable (hzero : ∀ g ∈ N, ∑ i, c.coord g i * k i = 0)
include hzero in
lemma parameter_kernel_le : (quotientParameterHom c hsk N hcomm).ker ≤ (linearParameterHom k).ker := by
  intro x hx
  have hxN : c.coord.symm x.toAdd ∈ N := (QuotientGroup.eq_one_iff _).mp hx
  apply Multiplicative.toAdd.injective
  have hz := hzero _ hxN
  simpa [linearParameterHom] using hz

def abelianCoordinateCharacter : G →* Multiplicative ℝ :=
  ((quotientParameterHom c hsk N hcomm).liftOfSurjective
    (quotientParameterHom_surjective c hsk N hcomm)
    ⟨linearParameterHom k,parameter_kernel_le c hsk N hcomm k hzero⟩).comp (QuotientGroup.mk' N)

lemma abelianCoordinateCharacter_apply (g : G) :
    Multiplicative.toAdd (abelianCoordinateCharacter c hsk N hcomm k hzero g) =
      ∑ i, c.coord g i * k i := by
  let x := Multiplicative.ofAdd (c.coord g)
  have hx : quotientParameterHom c hsk N hcomm x = QuotientGroup.mk g := by
    simp [quotientParameterHom,x]
  have hh := (quotientParameterHom c hsk N hcomm).liftOfRightInverse_comp_apply
    (Function.surjInv (quotientParameterHom_surjective c hsk N hcomm))
    (Function.rightInverse_surjInv (quotientParameterHom_surjective c hsk N hcomm))
    (⟨linearParameterHom k,parameter_kernel_le c hsk N hcomm k hzero⟩) x
  have hh' := congrArg Multiplicative.toAdd hh
  change Multiplicative.toAdd ((quotientParameterHom c hsk N hcomm).liftOfSurjective
    (quotientParameterHom_surjective c hsk N hcomm)
    ⟨linearParameterHom k,parameter_kernel_le c hsk N hcomm k hzero⟩
    (QuotientGroup.mk g)) = _
  simpa only [hx,linearParameterHom,MonoidHom.coe_mk,OneHom.coe_mk,toAdd_ofAdd,x] using hh'

lemma abelianCoordinateCharacter_continuous :
    Continuous (abelianCoordinateCharacter c hsk N hcomm k hzero) := by
  change Continuous (fun g => Multiplicative.ofAdd (Multiplicative.toAdd
    (abelianCoordinateCharacter c hsk N hcomm k hzero g)))
  simp_rw [abelianCoordinateCharacter_apply]
  exact continuous_ofAdd.comp (continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp c.coord.continuous).mul_const (k i)))

include hsk hcomm hzero in
lemma coordinate_form_mul (g h : G) :
    (∑ i, c.coord (g*h) i * k i) = (∑ i, c.coord g i * k i) + (∑ i, c.coord h i * k i) := by
  simp only [← abelianCoordinateCharacter_apply c hsk N hcomm k hzero,map_mul]
  rfl

end MalcevCharacters
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace RationalTailCoordinates
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+n)) (H : Subgroup G)
variable (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin (r+n), i.val < r → c.coord g i = 0)

lemma lift_single (i : Fin n) (t : ℝ) : lift r (Pi.single i t) = Pi.single (embed r i) t := by
  classical
  funext j
  by_cases hj : r ≤ j.val
  · simp only [lift,dite_eq_left hj,Pi.single_apply]
    have he : (⟨j.val-r,by have := j.isLt; omega⟩ : Fin n) = i ↔ j = embed r i := by
      constructor <;> intro he
      · apply Fin.ext
        have hh := congrArg Fin.val he
        change j.val-r = i.val at hh
        change j.val = r+i.val
        omega
      · have hh := congrArg Fin.val he
        apply Fin.ext
        change j.val = r+i.val at hh
        change j.val-r = i.val
        omega
    simp only [he]
  · have hne : j ≠ embed r i := by intro he; have hh := congrArg Fin.val he; simp [embed] at hh; omega
    simp [lift,hj,hne]

omit [IsTopologicalGroup G] in
lemma axis_val [IsTopologicalGroup G] (i : Fin n) (t : ℝ) :
    (axis (tailCoordinates c H hH) i t).val = axis c (embed r i) t := by
  change c.coord.symm (lift r (Pi.single i t)) = c.coord.symm (Pi.single (embed r i) t)
  rw [lift_single]

 

lemma tail_secondKind (hsk : SecondKind c) : SecondKind (tailCoordinates c H hH) where
  axis_add i s t := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,axis_val,hsk.axis_add]
  ordered g := by
    apply Subtype.ext
    change g.val = H.subtype (List.ofFn (fun i => axis (tailCoordinates c H hH) i
      ((tailCoordinates c H hH).coord g i)) |>.prod)
    rw [map_list_prod,List.map_ofFn]
    change g.val = (List.ofFn (fun i => (axis (tailCoordinates c H hH) i
      ((tailCoordinates c H hH).coord g i)).val)).prod
    simp only [axis_val]
    conv_lhs => rw [hsk.ordered g.val,List.ofFn_add,List.prod_append]
    have he : (List.ofFn (fun i : Fin r => axis c (i.castLE (Nat.le_add_right r n)) (c.coord g.val (i.castLE (Nat.le_add_right r n))))).prod = 1 := by
      have hzero : (fun i : Fin r => axis c (i.castLE (Nat.le_add_right r n)) (c.coord g.val (i.castLE (Nat.le_add_right r n)))) = fun _ => (1:G) := by
        funext i
        rw [(hH g.val).mp g.property _ i.isLt,axis_zero]
      rw [hzero]
      simp
    rw [he,one_mul]
    rfl

end RationalTailCoordinates

end
end
end
end
end

end OAI
