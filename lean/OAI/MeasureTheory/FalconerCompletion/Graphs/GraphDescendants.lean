import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphDegrees
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphJetMul
import OAI.MeasureTheory.FalconerCompletion.Sphere.ScalarCapPartition

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory
variable {d : ℕ}

noncomputable def graphDescendants (a p : ℕ) (X : CellPath d) : Finset (CellPath d) := by
  classical
  exact (dyadicPaths p).filter fun P => P.take a=X

noncomputable def graphChildren (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (a p : ℕ) (X : CellPath d) : Finset (CellPath d) := by
  classical
  exact (graphDescendants a p X).filter fun P => 0 < ρ (treeCell P)

lemma graphDescendants_subset {a p : ℕ} {X P : CellPath d} (hP : P ∈ graphDescendants a p X) :
    treeCell P ⊆ treeCell X := by
  classical
  rcases Finset.mem_filter.mp hP with ⟨hP,he⟩
  simpa only [he] using treeCell_subset_take P a

lemma graphDescendants_cover {a p : ℕ} (hap : a ≤ p) {X : CellPath d}
    (hX : X ∈ dyadicPaths a) :
    (⋃ P ∈ graphDescendants a p X, treeCell P)=treeCell X := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨P,hP,hx⟩ := Set.mem_iUnion₂.mp hx
    exact graphDescendants_subset hP hx
  · intro x hx
    have hxroot : x ∈ treeCell ([] : CellPath d) := by
      simpa only [List.take_zero] using treeCell_subset_take X 0 hx
    rw [←treeCell_cover_root p] at hxroot
    obtain ⟨P,hP,hxP⟩ := Set.mem_iUnion₂.mp hxroot
    have hlP : P.length=p := (mem_dyadicPaths _ _).mp hP
    have hlX : X.length=a := (mem_dyadicPaths _ _).mp hX
    have he : P.take a=X := by
      by_contra hne
      have hh := treeCell_disjoint (p:=P.take a) (q:=X)
        (by simp [List.length_take,hlP,hlX,Nat.min_eq_left hap]) hne
      exact Set.disjoint_left.mp hh (treeCell_subset_take P a hxP) hx
    exact Set.mem_iUnion₂.mpr ⟨P,Finset.mem_filter.mpr ⟨hP,he⟩,hxP⟩

lemma graphDescendants_disjoint {a p : ℕ} {X P Q : CellPath d}
    (hP : P ∈ graphDescendants a p X) (hQ : Q ∈ graphDescendants a p X) (hne : P ≠ Q) :
    Disjoint (treeCell P) (treeCell Q) := by
  classical
  apply treeCell_disjoint _ hne
  exact ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hP).1).trans
    ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hQ).1).symm

lemma graphChildren_integral (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {a p : ℕ} (hap : a ≤ p) {X : CellPath d} (hX : X ∈ dyadicPaths a)
    (F : EuclideanSpace ℝ (Fin d) → ℂ) (hF : IntegrableOn F (treeCell X) ρ) :
    (∫ x in treeCell X, F x ∂ρ) =
      ∑ P ∈ graphChildren ρ a p X, ∫ x in treeCell P, F x ∂ρ := by
  classical
  rw [←graphDescendants_cover hap hX]
  rw [integral_biUnion_finset _ (fun P _ => measurableSet_treeCell P)
    (fun P hP Q hQ hne => graphDescendants_disjoint hP hQ hne)
    (fun P hP => hF.mono_set (graphDescendants_subset hP))]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnP
  have hz : ρ (treeCell P)=0 := by
    apply le_antisymm _ bot_le
    by_contra hp
    exact hnP (Finset.mem_filter.mpr ⟨hP,lt_of_not_ge hp⟩)
  rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]

lemma graphChildren_mass (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) {X : CellPath d} (hX : X ∈ dyadicPaths a) :
    ∑ P ∈ graphChildren ρ a p X, ρ.real (treeCell P) = ρ.real (treeCell X) := by
  classical
  have h := graphChildren_integral ρ hap hX (fun _ => (1:ℂ)) (integrableOn_const (C:= (1:ℂ)))
  have hh := congrArg Complex.re h
  simpa [integral_const,Measure.real,Complex.re_sum] using hh.symm

lemma graphChildren_nonempty (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) {X : CellPath d} (hX : X ∈ dyadicPaths a)
    (hocc : 0 < ρ (treeCell X)) : (graphChildren ρ a p X).Nonempty := by
  have hm := graphChildren_mass ρ hap hX
  by_contra he
  rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hm
  have hp : 0 < ρ.real (treeCell X) := ENNReal.toReal_pos hocc.ne' (measure_ne_top _ _)
  linarith

lemma graphChildren_card_le (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) {X : CellPath d} (hX : X ∈ dyadicPaths a)
    {l u : ℝ} (hl : 0 < l)
    (hlo : ∀ P ∈ graphChildren ρ a p X, l ≤ ρ.real (treeCell P))
    (hup : ρ.real (treeCell X) ≤ u) :
    ((graphChildren ρ a p X).card : ℝ) ≤ u/l := by
  rw [le_div_iff₀ hl]
  calc
    _ = ∑ P ∈ graphChildren ρ a p X, l := by simp
    _ ≤ ∑ P ∈ graphChildren ρ a p X, ρ.real (treeCell P) := Finset.sum_le_sum hlo
    _ = ρ.real (treeCell X) := graphChildren_mass ρ hap hX
    _ ≤ u := hup

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory
open scoped RealInnerProductSpace
variable {d : ℕ}

lemma treeCell_diameter {P : CellPath d} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ treeCell P) (hy : y ∈ treeCell P) :
    ‖x-y‖ ≤ (d+1:ℝ)*(2:ℝ)^(-(P.length:ℝ)) := by
  have h := ambientGridCell_dist_le hy hx
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  simpa only [dist_eq_norm,div_eq_mul_inv] using h

lemma graphChildren_length {ρ : Measure (EuclideanSpace ℝ (Fin d))} {a p : ℕ} {X P : CellPath d}
    (hP : P ∈ graphChildren ρ a p X) : P.length=p := by
  classical
  exact (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1

lemma graphChildren_subset {ρ : Measure (EuclideanSpace ℝ (Fin d))} {a p : ℕ} {X P : CellPath d}
    (hP : P ∈ graphChildren ρ a p X) : treeCell P ⊆ treeCell X := by
  classical
  exact graphDescendants_subset (Finset.mem_filter.mp hP).1

lemma graphChildren_center_error {ρ κ : Measure (EuclideanSpace ℝ (Fin d))} {a p : ℕ}
    {X Y P Q : CellPath d} (hP : P ∈ graphChildren ρ a p X) (hQ : Q ∈ graphChildren κ a p Y)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell P) (hy : y ∈ treeCell Q) :
    ‖(x-y)-(treeCenter P-treeCenter Q)‖ ≤ 2*(d+1:ℝ)*(2:ℝ)^(-(p:ℝ)) := by
  have hx' := treeCell_diameter hx (treeCenter_mem P)
  have hy' := treeCell_diameter hy (treeCenter_mem Q)
  rw [graphChildren_length hP] at hx'
  rw [graphChildren_length hQ] at hy'
  calc
    _ = ‖(x-treeCenter P)-(y-treeCenter Q)‖ := by congr 1; module
    _ ≤ ‖x-treeCenter P‖+‖y-treeCenter Q‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma graphChildren_direct_size {ρ κ : Measure (EuclideanSpace ℝ (Fin d))} {a p : ℕ}
    {X P Q : CellPath d} (hX : X ∈ dyadicPaths a)
    (hP : P ∈ graphChildren ρ a p X) (hQ : Q ∈ graphChildren κ a p X)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell P) (hy : y ∈ treeCell Q) :
    ‖x-y‖ ≤ (d+1:ℝ)*(2:ℝ)^(-(a:ℝ)) := by
  simpa only [(mem_dyadicPaths _ _).mp hX] using
    treeCell_diameter (graphChildren_subset hP hx) (graphChildren_subset hQ hy)

lemma graphChildren_cross_size {ρ κ : Measure (EuclideanSpace ℝ (Fin d))} {a p : ℕ}
    {X Y P Q : CellPath d} (hX : X ∈ dyadicPaths a) (hY : Y ∈ dyadicPaths a)
    (hP : P ∈ graphChildren ρ a p X) (hQ : Q ∈ graphChildren κ a p Y)
    {G : ℝ} (hcenters : ‖treeCenter X-treeCenter Y‖ ≤ G*(2:ℝ)^(-(a:ℝ)))
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell P) (hy : y ∈ treeCell Q) :
    ‖x-y‖ ≤ (2*(d+1:ℝ)+G)*(2:ℝ)^(-(a:ℝ)) := by
  have hx' := treeCell_diameter (graphChildren_subset hP hx) (treeCenter_mem X)
  have hy' := treeCell_diameter (treeCenter_mem Y) (graphChildren_subset hQ hy)
  rw [(mem_dyadicPaths _ _).mp hX] at hx'
  rw [(mem_dyadicPaths _ _).mp hY] at hy'
  calc
    _ = ‖(x-treeCenter X)+(treeCenter X-treeCenter Y)+(treeCenter Y-y)‖ := by congr 1; module
    _ ≤ ‖x-treeCenter X‖+‖treeCenter X-treeCenter Y‖+‖treeCenter Y-y‖ := norm_add₃_le
    _ ≤ _ := by linarith

lemma graphChildren_profile_card (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) {X : CellPath d} (hX : X ∈ dyadicPaths a)
    {R ma mp e : ℝ} (hR : 0 < R)
    (hlo : ∀ P ∈ graphChildren ρ a p X, R^(-mp-e) ≤ ρ.real (treeCell P))
    (hup : ρ.real (treeCell X) ≤ R^(-ma+e)) :
    ((graphChildren ρ a p X).card : ℝ) ≤ R^(mp-ma+2*e) := by
  have h := graphChildren_card_le ρ hap hX (Real.rpow_pos_of_pos hR _) hlo hup
  rw [←Real.rpow_sub hR] at h
  convert h using 1; ring_nf

lemma graphChildren_pair_profile_card
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {a p : ℕ} (hap : a ≤ p) {X Y : CellPath d} (hX : X ∈ dyadicPaths a) (hY : Y ∈ dyadicPaths a)
    {R ma₁ mp₁ ma₂ mp₂ e : ℝ} (hR : 0 < R)
    (hlo₁ : ∀ P ∈ graphChildren ρ a p X, R^(-mp₁-e) ≤ ρ.real (treeCell P))
    (hlo₂ : ∀ P ∈ graphChildren κ a p Y, R^(-mp₂-e) ≤ κ.real (treeCell P))
    (hup₁ : ρ.real (treeCell X) ≤ R^(-ma₁+e))
    (hup₂ : κ.real (treeCell Y) ≤ R^(-ma₂+e)) :
    (graphChildren ρ a p X).card * ((graphChildren κ a p Y).card:ℝ) ≤
      R^((mp₁-ma₁)+(mp₂-ma₂)+4*e) := by
  have h₁ := graphChildren_profile_card ρ hap hX hR hlo₁ hup₁
  have h₂ := graphChildren_profile_card κ hap hY hR hlo₂ hup₂
  calc
    _ ≤ R^(mp₁-ma₁+2*e)*R^(mp₂-ma₂+2*e) := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hR]; congr 1; ring

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory
variable {d : ℕ}

lemma tensorCapND_nonneg (δ : ℝ) (a : Fin d → ℤ) (w : EuclideanSpace ℝ (Fin d)) :
    0 ≤ tensorCapND δ a w := tensorCapKernelND_nonneg _ _

lemma tensorCapND_le_one (δ : ℝ) (a : Fin d → ℤ) (w : EuclideanSpace ℝ (Fin d)) :
    tensorCapND δ a w ≤ 1 := tensorCapKernelND_le_one _ _

lemma sphereCapGridND_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((sphereCapGridND d δ).card : ℝ) ≤ (9*δ⁻¹)^d := by
  classical
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hceil : (⌈δ⁻¹⌉:ℝ) < δ⁻¹+1 := Int.ceil_lt_add_one _
  have hci : (0:ℤ) ≤ ⌈δ⁻¹⌉ := Int.ceil_nonneg (by positivity)
  have hfull : ((fullCapGridND d δ).card : ℝ) = (2*(⌈δ⁻¹⌉:ℝ)+5)^d := by
    simp only [fullCapGridND, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.cast_pow, Int.card_Icc]
    have he : ((⌈δ⁻¹⌉+2+1- -(⌈δ⁻¹⌉+2)).toNat : ℝ) =
        ((⌈δ⁻¹⌉+2+1- -(⌈δ⁻¹⌉+2) : ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌈δ⁻¹⌉+2+1- -(⌈δ⁻¹⌉+2) by omega)
    rw [he]
    push_cast
    ring
  calc
    _ ≤ ((fullCapGridND d δ).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (fullCapGridND d δ) _
    _ = _ := hfull
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) d

lemma sphereCap_pair_partition {δ : ℝ} (hδ : 0 < δ)
    (hs : (d+1:ℝ)*δ ≤ 1/2) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (hz : ‖z.1‖=1 ∧ ‖z.2‖=1) :
    (∀ k ∈ (sphereCapGridND d δ).product (sphereCapGridND d δ),
      0 ≤ tensorCapND δ k.1 z.1*tensorCapND δ k.2 z.2) ∧
    ∑ k ∈ (sphereCapGridND d δ).product (sphereCapGridND d δ),
      tensorCapND δ k.1 z.1*tensorCapND δ k.2 z.2 = 1 := by
  classical
  constructor
  · intro k _; positivity [tensorCapND_nonneg δ k.1 z.1,tensorCapND_nonneg δ k.2 z.2]
  · calc
      _ = ∑ i ∈ sphereCapGridND d δ, ∑ j ∈ sphereCapGridND d δ,
          tensorCapND δ i z.1*tensorCapND δ j z.2 :=
        Finset.sum_product _ _ _
      _ = (∑ i ∈ sphereCapGridND d δ, tensorCapND δ i z.1)*
          (∑ j ∈ sphereCapGridND d δ, tensorCapND δ j z.2) := (Finset.sum_mul_sum _ _ _ _).symm
      _ = 1 := by rw [sphereCapGridND_partition hδ hs z.1 hz.1,
        sphereCapGridND_partition hδ hs z.2 hz.2,one_mul]

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

structure GraphSymbolJet (b : V → V → ℂ) (m : ℕ) (s B : ℝ) : Prop where
  measurable : Measurable (Function.uncurry b)
  smooth : ∀ x, ContDiff ℝ ∞ (b x)
  nonneg : 0 ≤ B
  bound : ∀ x j, j ≤ m → ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖ ≤ B*s^j

omit [FiniteDimensional ℝ V] [BorelSpace V] in
lemma GraphSymbolJet.norm_le {b : V → V → ℂ} {m : ℕ} {s B : ℝ}
    (h : GraphSymbolJet b m s B) (x w : V) (hw : ‖w‖=1) : ‖b x w‖ ≤ B := by
  simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using h.bound x 0 (Nat.zero_le _) w hw

lemma graph_uneligible_transform (ρ σ : Measure V) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (P : Set V) (M : ℝ) (η : V → ℝ) (b : V → V → ℂ)
    (hη : Measurable η) (hb : Measurable (Function.uncurry b))
    {E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hη0 : ∀ᵐ w ∂σ, 0 ≤ η w) (hηE : ∀ᵐ w ∂σ, η w ≤ E)
    (hbB : ∀ᵐ w ∂σ, ∀ x, ‖b x w‖ ≤ B)
    (hz : ¬0 < ∫ x in P, ∫ w, η w*‖b x w‖^2 ∂σ ∂ρ) :
    ∀ᵐ w ∂σ, η w=0 ∨ ∀ r, sourceAngularTransformND ρ P M b r w=0 := by
  have hz' := zero_cap_energy_transform (ρ.restrict P) σ η b hη hb hE hB hη0 hηE hbB
    (le_antisymm (not_lt.mp hz) (cap_energy_nonneg _ _ _ _ hη0))
  filter_upwards [hz'] with w hw
  rcases hw with hw | hw
  · exact Or.inl hw
  right
  intro r
  have hr := hw r
  simp only [sourceAngularTransformND,inv_one,one_smul,Measure.restrict_univ] at hr
  simp only [sourceAngularTransformND,hr,smul_zero]

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory
variable {d : ℕ}

lemma graphChildren_eligible_iff {ρ : Measure (EuclideanSpace ℝ (Fin d))} {a p : ℕ}
    {X P : CellPath d} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    (hP : P ∈ graphChildren ρ a p X) :
    P ∈ eligibleCells ρ a p X η b ↔ 0 < cellCapEnergy ρ P η b := by
  classical
  have hP' := Finset.mem_filter.mp (Finset.mem_filter.mp hP).1
  simp only [eligibleCells,Finset.mem_filter,hP'.1,hP'.2,true_and]

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma graphCellLaw_four_ae (ρ₁ ρ₂ ρ₃ ρ₄ : Measure V)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] [IsFiniteMeasure ρ₃] [IsFiniteMeasure ρ₄]
    (P₁ P₂ P₃ P₄ : Set V) (M₁ M₂ M₃ M₄ : ℝ)
    (hP₁ : MeasurableSet P₁) (hP₂ : MeasurableSet P₂)
    (hP₃ : MeasurableSet P₃) (hP₄ : MeasurableSet P₄) :
    ∀ᵐ z ∂((graphCellLaw ρ₁ P₁ M₁).prod (graphCellLaw ρ₂ P₂ M₂)).prod
      ((graphCellLaw ρ₃ P₃ M₃).prod (graphCellLaw ρ₄ P₄ M₄)),
      z.1.1 ∈ P₁ ∧ z.1.2 ∈ P₂ ∧ z.2.1 ∈ P₃ ∧ z.2.2 ∈ P₄ := by
  have h₁₂ : ∀ᵐ z ∂(graphCellLaw ρ₁ P₁ M₁).prod (graphCellLaw ρ₂ P₂ M₂),
      z.1 ∈ P₁ ∧ z.2 ∈ P₂ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (graphCellLaw_ae ρ₁ hP₁ M₁),
      Measure.quasiMeasurePreserving_snd.ae (graphCellLaw_ae ρ₂ hP₂ M₂)] with z h₁ h₂
    exact ⟨h₁,h₂⟩
  have h₃₄ : ∀ᵐ z ∂(graphCellLaw ρ₃ P₃ M₃).prod (graphCellLaw ρ₄ P₄ M₄),
      z.1 ∈ P₃ ∧ z.2 ∈ P₄ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (graphCellLaw_ae ρ₃ hP₃ M₃),
      Measure.quasiMeasurePreserving_snd.ae (graphCellLaw_ae ρ₄ hP₄ M₄)] with z h₃ h₄
    exact ⟨h₃,h₄⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h₁₂,
    Measure.quasiMeasurePreserving_snd.ae h₃₄] with z h₁₂ h₃₄
  exact ⟨h₁₂.1,h₁₂.2,h₃₄.1,h₃₄.2⟩

lemma graph_radial_budget {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : HasCompactSupport Ψ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ (∫ u : ℝ, ‖(Ψ u:ℂ)‖) ≤ K ∧
      ∀ u, ‖iteratedDeriv m (fun u => (Ψ u:ℂ)) u‖ ≤ K := by
  let f : ℝ → ℂ := fun u => (Ψ u:ℂ)
  have hts : tsupport f = tsupport Ψ := by
    change closure (Function.support f) = closure (Function.support Ψ)
    congr 1
    ext u
    simp only [Function.mem_support, f, ne_eq, Complex.ofReal_eq_zero]
  have hs' : HasCompactSupport f := by
    change IsCompact (tsupport f)
    rw [hts]
    exact hs
  have hΨ' : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hΨ
  obtain ⟨K,hK⟩ := (hs'.iteratedFDeriv m).exists_bound_of_continuous
    (hΨ'.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (m:ℕ∞) ≤ ⊤)))
  refine ⟨max K (∫ u, ‖f u‖), (integral_nonneg (fun _ => norm_nonneg _)).trans (le_max_right _ _),
    le_max_right _ _,?_⟩
  intro u
  rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hK u).trans (le_max_left _ _)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
lemma graph_symbol_pair_budget {b c : V → V → ℂ} {θ : V → ℂ}
    {m : ℕ} {s A B C P : ℝ} (hb : GraphSymbolJet b m s B) (hc : GraphSymbolJet c m s C)
    (hθ : ContDiff ℝ ∞ θ) (hs : 0 ≤ s) (hsA : s ≤ A) (hP : 0 ≤ P)
    (hdθ : ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j θ w‖ ≤ P*A^j) :
    (∀ z, ContDiff ℝ ∞ (graphPairAmplitude θ b c z)) ∧
    ∀ z j, j ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (graphPairAmplitude θ b c z) w‖ ≤
        (P*B*2^m*C*2^m)*A^j := by
  constructor
  · intro z; exact (hθ.mul (hb.smooth z.1)).mul (Complex.conjCLE.contDiff.comp (hc.smooth z.2))
  · intro z j hj w hw
    exact graphJetPair hθ (hb.smooth z.1) (hc.smooth z.2) m hP hb.nonneg hc.nonneg
      (hs.trans hsA) w (fun k hk => hdθ k hk w hw)
      (graphJet_enlarge hb.nonneg hs hsA (fun k hk => hb.bound z.1 k hk w hw))
      (graphJet_enlarge hc.nonneg hs hsA (fun k hk => hc.bound z.2 k hk w hw)) j hj

end CurrentFalconer
end
end

end OAI
