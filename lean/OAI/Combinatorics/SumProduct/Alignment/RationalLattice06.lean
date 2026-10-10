import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerHyperplane01
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
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

lemma realPower_int (g : G) (z : ℤ) : realPower c g z = g^z := by
  cases z with
  | ofNat m => simpa using realPower_nat c g m
  | negSucc m =>
    rw [Int.cast_negSucc,realPower_neg]
    simp only [realPower_nat,zpow_negSucc]

lemma basisElement_rational (i : Fin n) : IsRational c (basisElement c i) := by
  classical
  intro j
  refine ⟨if j=i then 1 else 0,?_⟩
  simp only [basisElement,Homeomorph.apply_symm_apply,Pi.single_apply]
  split_ifs <;> simp

lemma basisFlow_rational (i : Fin n) (t : ℚ) : IsRational c (basisFlow c i t) :=
  realPower_rational c (basisElement_rational c i) t

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
include hΓ

lemma basisElement_mem (i : Fin n) : basisElement c i ∈ Γ := by
  classical
  apply (hΓ _).mpr
  intro j
  refine ⟨if j=i then 1 else 0,?_⟩
  simp only [basisElement,Homeomorph.apply_symm_apply,Pi.single_apply]
  split_ifs <;> simp

lemma basisFlow_int_mem (i : Fin n) (t : ℤ) : basisFlow c i t ∈ Γ := by
  change realPower c (basisElement c i) t ∈ Γ
  rw [realPower_int]
  exact Γ.zpow_mem (basisElement_mem c Γ hΓ i) _

lemma peel_mem_lattice {g : G} (hg : g ∈ Γ) (k : ℕ) : peel c g k ∈ Γ := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    simp only [peel]
    split_ifs with hk
    · obtain ⟨z,hz⟩ := (hΓ _).mp ih ⟨k,hk⟩
      rw [hz,← Int.cast_neg]
      exact Γ.mul_mem (basisFlow_int_mem c Γ hΓ _ _) ih
    · exact ih

 

theorem expCoordinates_lattice (g : G) :
    g ∈ Γ ↔ ∀ i, ∃ z : ℤ, expCoordinates c g i = z := by
  constructor
  · intro hg i
    exact (hΓ _).mp (peel_mem_lattice c Γ hΓ hg i.val) i
  · intro hg
    rw [← expProduct_expCoordinates c g]
    change (List.ofFn (fun i => basisFlow c i (expCoordinates c g i))).prod ∈ Γ
    apply list_prod_mem
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨z,hz⟩ := hg i
    rw [hz]
    exact basisFlow_int_mem c Γ hΓ i z

omit hΓ in
 

theorem character_expCoordinates (χ : G →* Multiplicative ℝ) (hχ : Continuous χ) (g : G) :
    Multiplicative.toAdd (χ g) =
      ∑ i, expCoordinates c g i * Multiplicative.toAdd (χ (basisElement c i)) := by
  conv_lhs => rw [← expProduct_expCoordinates c g]
  change Multiplicative.toAdd (χ ((List.ofFn (fun i =>
    basisFlow c i (expCoordinates c g i))).prod)) = _
  rw [map_list_prod,List.map_ofFn]
  simp only [toAdd_list_sum,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact character_realPower c χ hχ _ _

 

theorem integer_character_expCoordinates (χ : G →* Multiplicative ℝ) (hχ : Continuous χ)
    (hz : ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z) :
    ∃ k : Fin n → ℤ, ∀ g : G, Multiplicative.toAdd (χ g) =
      ∑ i, expCoordinates c g i * (k i : ℝ) := by
  choose k hk using (fun i => hz _ (basisElement_mem c Γ hΓ i))
  refine ⟨k,fun g => ?_⟩
  rw [character_expCoordinates c χ hχ]
  simp_rw [hk]

end RationalLattice
end
end
 

 
section
open Set Topology
noncomputable section
namespace CharacterKernelLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (χ : G →* Multiplicative ℝ) (hχ : Continuous χ)
variable (Γ : Subgroup G) (C : Set G) (hC : IsCompact C)
variable (hreps : ∀ g : G, ∃ c ∈ C, c⁻¹*g ∈ Γ)
variable (hZ : ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z)
include hχ hC hreps hZ

 

theorem compact_kernel_representatives :
    ∃ D : Set G, IsCompact D ∧ D ⊆ χ.ker ∧
      ∀ g ∈ χ.ker, ∃ d ∈ D, d⁻¹*g ∈ Γ := by
  classical
  let p : G → ℝ := fun g => Multiplicative.toAdd (χ g)
  have hp : Continuous p := hχ
  let J : Set ℤ := {z | (z : ℝ) ∈ p '' C ∧ ∃ γ ∈ Γ, p γ = z}
  have hJ : J.Finite := by
    apply Set.Finite.subset ((Int.isClosedEmbedding_coe_real.isCompact_preimage (hC.image hp)).finite ⟨inferInstance⟩)
    exact fun z hz => hz.1
  have hex (z : J) : ∃ γ ∈ Γ, p γ = (z.val : ℝ) := z.property.2
  choose δ hδΓ hδp using hex
  let D : Set G := ⋃ z : J, (fun c => c * (δ z)⁻¹) '' (C ∩ {c | p c = (z.val : ℝ)})
  refine ⟨D,?_,?_,?_⟩
  · have : Finite J := hJ.to_subtype
    exact isCompact_iUnion fun z => (hC.inter_right (isClosed_eq hp continuous_const)).image
      (continuous_id.mul continuous_const)
  · intro d hd
    obtain ⟨z,c,hc,rfl⟩ := Set.mem_iUnion.mp hd
    change χ (c*(δ z)⁻¹) = 1
    apply Multiplicative.toAdd.injective
    change p (c*(δ z)⁻¹) = 0
    change Multiplicative.toAdd (χ (c*(δ z)⁻¹)) = 0
    rw [map_mul,map_inv]
    change p c - p (δ z) = 0
    rw [hc.2,hδp]
    exact sub_self _
  · intro g hg
    obtain ⟨c,hc,hcg⟩ := hreps g
    obtain ⟨z,hz⟩ := hZ (c⁻¹*g) hcg
    have hp0 : p g = 0 := hg
    have hpc : p c = (-z : ℤ) := by
      have hh : p (c⁻¹*g) = -p c + p g := by
        dsimp [p]; rw [map_mul,map_inv]; rfl
      change p (c⁻¹*g) = (z : ℝ) at hz
      rw [hh,hp0,add_zero] at hz
      push_cast
      linarith
    have hzJ : (-z) ∈ J := by
      refine ⟨⟨c,hc,hpc⟩, (c⁻¹*g)⁻¹,Γ.inv_mem hcg,?_⟩
      change Multiplicative.toAdd (χ ((c⁻¹*g)⁻¹)) = _
      rw [map_inv]
      change -Multiplicative.toAdd (χ (c⁻¹*g)) = _
      rw [hz]
      simp
    let j : J := ⟨-z,hzJ⟩
    refine ⟨c*(δ j)⁻¹,Set.mem_iUnion.mpr ⟨j,c,⟨hc,hpc⟩,rfl⟩,?_⟩
    have he : (c*(δ j)⁻¹)⁻¹*g = δ j*(c⁻¹*g) := by group
    rw [he]
    exact Γ.mul_mem (hδΓ j) hcg

 

theorem compact_kernel_representatives_inter :
    ∃ D : Set G, IsCompact D ∧ D ⊆ χ.ker ∧
      ∀ g ∈ χ.ker, ∃ d ∈ D, d⁻¹*g ∈ Γ ⊓ χ.ker := by
  obtain ⟨D,hD,hDK,hrep⟩ := compact_kernel_representatives χ hχ Γ C hC hreps hZ
  refine ⟨D,hD,hDK,fun g hg => ?_⟩
  obtain ⟨d,hd,hdg⟩ := hrep g hg
  exact ⟨d,hd,hdg,χ.ker.mul_mem (χ.ker.inv_mem (hDK hd)) hg⟩

end CharacterKernelLattice
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevCharacters
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)

include hsk in
omit [IsTopologicalGroup G] in
lemma character_ext_coordinates {χ ψ : G →* Multiplicative ℝ}
    (hχ : Continuous χ) (hψ : Continuous ψ)
    (he : ∀ i, χ (axis c i 1) = ψ (axis c i 1)) : χ = ψ := by
  ext g
  apply Multiplicative.toAdd.injective
  rw [character_coordinates c hsk χ hχ,character_coordinates c hsk ψ hψ]
  simp_rw [he]

include hsk in
 

omit [IsTopologicalGroup G] in
theorem bounded_integral_characters_finite (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z) (A : ℝ) :
    {χ : G →* Multiplicative ℝ | Continuous χ ∧
      (∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z) ∧
      ∀ i, |Multiplicative.toAdd (χ (axis c i 1))| ≤ A}.Finite := by
  classical
  let S : Set ℝ := (Int.cast : ℤ → ℝ) '' {z : ℤ | |(z : ℝ)| ≤ A}
  have hs : S.Finite := by
    apply Set.Finite.image
    have hc := Int.isClosedEmbedding_coe_real.isCompact_preimage
      (isCompact_closedBall (0 : ℝ) A)
    have hf := hc.finite (show IsDiscrete ((Int.cast : ℤ → ℝ) ⁻¹' Metric.closedBall 0 A) from ⟨inferInstance⟩)
    simpa only [Set.preimage_ofPred_eq, Metric.closedBall, dist_zero_right,Real.norm_eq_abs] using hf
  let f (χ : G →* Multiplicative ℝ) (i : Fin n) := Multiplicative.toAdd (χ (axis c i 1))
  apply Set.Finite.of_finite_image (f := f)
  · apply (Set.Finite.pi' (fun _ : Fin n => hs)).subset
    rintro y ⟨χ,hχ,rfl⟩ i
    obtain ⟨z,hz⟩ := hχ.2.1 _ (axis_one_mem c Γ hΓ i)
    exact ⟨z,by simpa [← hz] using hχ.2.2 i,hz.symm⟩
  · intro χ hχ ψ hψ he
    apply character_ext_coordinates c hsk hχ.1 hψ.1
    intro i
    exact Multiplicative.toAdd.injective (congrFun he i)

variable (χ : G →* Multiplicative ℝ) (hχ : Continuous χ)
include hsk hχ

 

omit [IsTopologicalGroup G] in
theorem kernel_inter_connected (H : Subgroup G) (V : Submodule ℝ (Fin n → ℝ))
    (hV : ∀ g : G, g ∈ H ↔ c.coord g ∈ V) : IsConnected (↑H ∩ (χ.ker : Set G)) := by
  let W := V ⊓ (coordinateForm (fun i => Multiplicative.toAdd (χ (axis c i 1)))).ker
  have he : (↑H ∩ (χ.ker : Set G)) = c.coord.symm '' (W : Set (Fin n → ℝ)) := by
    ext g
    constructor
    · intro hg
      refine ⟨c.coord g,⟨(hV g).mp hg.1,?_⟩,c.coord.symm_apply_apply g⟩
      change (∑ i, c.coord g i * Multiplicative.toAdd (χ (axis c i 1))) = 0
      rw [← character_coordinates c hsk χ hχ g]
      exact congrArg Multiplicative.toAdd hg.2
    · rintro ⟨x,hx,rfl⟩
      refine ⟨(hV _).mpr (by simpa using hx.1),?_⟩
      apply Multiplicative.toAdd.injective
      rw [character_coordinates c hsk χ hχ]
      simpa [coordinateForm] using hx.2
  rw [he]
  exact (W.convex.isConnected ⟨0,by simp⟩).image _ c.coord.symm.continuous.continuousOn

 

omit [IsTopologicalGroup G] in
theorem nontrivial_kernel_geometry (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (hz : ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z) (hne : χ ≠ 1) :
    ∃ k : Fin n → ℤ, k ≠ 0 ∧
      (∀ g, Multiplicative.toAdd (χ g) = ∑ i, c.coord g i * (k i : ℝ)) ∧
      (χ.ker : Set G) = c.coord.symm '' ((IntegerHyperplane.form k).ker : Set (Fin n → ℝ)) ∧
      Module.finrank ℝ (IntegerHyperplane.form k).ker = n-1 := by
  obtain ⟨k,hk⟩ := integer_character_coordinates c hsk χ Γ hΓ hχ hz
  have hk0 : k ≠ 0 := by
    intro he
    apply hne
    ext g
    apply Multiplicative.toAdd.injective
    rw [hk,he]
    simp
  refine ⟨k,hk0,hk,?_,IntegerHyperplane.kernel_finrank k hk0⟩
  ext g
  constructor
  · intro hg
    refine ⟨c.coord g,?_,c.coord.symm_apply_apply g⟩
    change (∑ i, (k i : ℝ) * c.coord g i) = 0
    rw [Finset.sum_congr rfl (fun i _ => mul_comm _ _), ← hk]
    exact congrArg Multiplicative.toAdd hg
  · rintro ⟨x,hx,rfl⟩
    apply Multiplicative.toAdd.injective
    rw [hk]
    simpa [IntegerHyperplane.form,mul_comm] using hx

end MalcevCharacters

end
end
end
end
end

end OAI
