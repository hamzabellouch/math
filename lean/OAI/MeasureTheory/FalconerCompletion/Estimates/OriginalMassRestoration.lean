import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Measures.AssemblyTestFailures
import OAI.MeasureTheory.FalconerCompletion.Measures.MaskedPushforwardDeficit
import OAI.MeasureTheory.FalconerCompletion.Recursion.AssemblyDescriptorListCard

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped Classical ENNReal

theorem actual_original_mass_restoration (n : ℕ) (_hn : 1 ≤ n) (sig : ℝ) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
      ∀ (μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B : ℕ) (chi : ℝ) (F : AssemblyClassFamily ι μ N B chi sig)
        (G : AssemblyClassFamily κ ν N B chi sig),
      ∀ kap beta : ℝ, 0 < kap → 0 < beta →
      ∀ Γ good : Set ((EuclideanSpace ℝ (Fin (n+1))) × (EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet Γ → MeasurableSet good → good ⊆ Γ →
      Γ ⊆ treeCell [] ×ˢ treeCell [] →
      ∀ δ : ℝ, 0 < δ → (∀ z ∈ Γ, δ ≤ dist z.1 z.2) →
      (∀ᵐ x ∂μ, ∀ w : EuclideanSpace ℝ (Fin (n+1)), ‖w‖=1 → ∀ r : ℝ,
        ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {y | (x,y)∈good ∧ radialVector x y ∈ ball w r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((n+1:ℝ)/2))) →
      (∀ᵐ y ∂ν, ∀ w : EuclideanSpace ℝ (Fin (n+1)), ‖w‖=1 → ∀ r : ℝ,
        ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | (x,y)∈good ∧ radialVector x y ∈ ball w r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((n+1:ℝ)/2))) →
      let Ctest : ℝ := 1000*(n+2:ℝ)
      let α := _root_.OAI.CurrentFalconer.AssemblyLimit.filteredDistanceMeasure μ ν Γ
      let τ := ((μ.prod ν).withDensity (fun z => ENNReal.ofReal
        ((dist z.1 z.2)^(-(n:ℝ)/2) * Γ.indicator (assemblyTheta F G kap Ctest beta) z))).map
            (fun z => dist z.1 z.2)
      τ ≤ α ∧ (α-τ) univ ≤ ENNReal.ofReal (δ^(-(n:ℝ)/2)) *
        (μ (⋃ i, F.domain i)ᶜ + ν (⋃ j, G.domain j)ᶜ + (μ.prod ν) (Γ\good) +
          ENNReal.ofReal (((Fintype.card ι + Fintype.card κ:ℕ):ℝ)*
            ((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig)))
 := by
  classical
  obtain ⟨N₀,hfamily⟩ := uniform_original_family_failure_bound (n:=n) sig hsig
  refine ⟨max 1 N₀,?_⟩
  intro N hN ι κ _ _ μ ν _ _ B chi F G kap beta hkap hbeta Γ good hΓ hgood hgΓ hroot
    δ hδ hsep hcap₁ hcap₂
  dsimp only
  let C : ℝ := 1000*(n+2:ℝ)
  let J := sourceSmoothingLevels sig kap
  let q := sourcePolicyBlock N kap
  let K : ℕ := (N+1)^3+1
  let L : ι → κ → Finset PolicyDescriptor := fun i j =>
    assemblyDescriptorList (F.env kap C i).profile N q (assemblyPairEntry F G kap C beta i j)
  let R : κ → ι → Finset PolicyDescriptor := fun j i =>
    assemblyDescriptorList (G.env kap C j).profile N q (assemblyPairEntry F G kap C beta i j)
  let dir : (EuclideanSpace ℝ (Fin (n+1))) × (EuclideanSpace ℝ (Fin (n+1))) →
      EuclideanSpace ℝ (Fin (n+1)) := fun z => radialVector z.1 z.2
  have hdir : Measurable dir := measurable_radialVector
  have hunit : ∀ z∈good, ‖dir z‖=1 := by
    intro z hz
    apply norm_radialVector
    intro he
    have hh := hsep z (hgΓ hz)
    rw [he,dist_self] at hh
    exact (not_le_of_gt hδ) hh
  have hq : 0<q := sourcePolicyBlock_pos (by omega) hkap
  have hc (i : ι) (j : κ) := assemblyPairEntry_le F G kap C beta hbeta i j
  have hLv : ∀ i j b, b∈L i j → descriptorValid N b := by
    intro i j b hb
    exact assemblyDescriptorList_valid _ hq (hc i j) hb
  have hRv : ∀ j i b, b∈R j i → descriptorValid N b := by
    intro j i b hb
    exact assemblyDescriptorList_valid _ hq (hc i j) hb
  have hLc (i : ι) (j : κ) : (L i j).card≤K := assemblyDescriptorList_card _ hq
  have hRc (j : κ) (i : ι) : (R j i).card≤K := assemblyDescriptorList_card _ hq
  let badL := assemblyTestFailures F J good dir L
  let badR₀ := assemblyTestFailures G J (Prod.swap ⁻¹' good) (dir ∘ Prod.swap) R
  let badR := Prod.swap ⁻¹' badR₀
  have hmL : MeasurableSet badL := assemblyTestFailures_measurable F J good hgood dir hdir L
  have hmR₀ : MeasurableSet badR₀ := assemblyTestFailures_measurable G J _
    (hgood.preimage measurable_swap) _ (hdir.comp measurable_swap) R
  have hmR : MeasurableSet badR := hmR₀.preimage measurable_swap
  have hbadL : (μ.prod ν) badL ≤ ENNReal.ofReal ((Fintype.card κ:ℝ)*(K:ℝ)*((2:ℝ)^N)^(-sig)) :=
    hfamily N (by omega) μ ν B chi F good hgood dir hdir hunit hcap₁ J K L hLv hLc
  have hbadR₀ : (ν.prod μ) badR₀ ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*(K:ℝ)*((2:ℝ)^N)^(-sig)) := by
    apply hfamily N (by omega) ν μ B chi G (Prod.swap ⁻¹' good) (hgood.preimage measurable_swap)
      (dir ∘ Prod.swap) (hdir.comp measurable_swap) (fun z hz => hunit _ hz) ?_ J K R hRv hRc
    simpa only [mem_preimage,Function.comp_def,Prod.swap_prod_mk] using hcap₂
  have hbadR : (μ.prod ν) badR ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*(K:ℝ)*((2:ℝ)^N)^(-sig)) := by
    have he : (μ.prod ν) badR = (ν.prod μ) badR₀ := by
      rw [←Measure.map_apply measurable_swap hmR₀,Measure.prod_swap]
    rw [he]
    exact hbadR₀
  let discarded₁ : Set (EuclideanSpace ℝ (Fin (n+1))) := (⋃ i,F.domain i)ᶜ
  let discarded₂ : Set (EuclideanSpace ℝ (Fin (n+1))) := (⋃ j,G.domain j)ᶜ
  let bad := (discarded₁ ×ˢ univ) ∪ (univ ×ˢ discarded₂) ∪ (Γ\good) ∪ badL ∪ badR
  have hmD₁ : MeasurableSet discarded₁ := (MeasurableSet.iUnion F.measurable).compl
  have hmD₂ : MeasurableSet discarded₂ := (MeasurableSet.iUnion G.measurable).compl
  have hmbad : MeasurableSet bad :=
    ((((hmD₁.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hmD₂)).union
      (hΓ.diff hgood)).union hmL).union hmR
  have hmass : (μ.prod ν) bad ≤ μ discarded₁ + ν discarded₂ + (μ.prod ν) (Γ\good) +
      ENNReal.ofReal (((Fintype.card ι+Fintype.card κ:ℕ):ℝ)*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig)) := by
    have hu₁ := measure_union_le (μ:=μ.prod ν) (discarded₁ ×ˢ univ) (univ ×ˢ discarded₂)
    have hu₂ := measure_union_le (μ:=μ.prod ν) ((discarded₁ ×ˢ univ) ∪ (univ ×ˢ discarded₂)) (Γ\good)
    have hu₃ := measure_union_le (μ:=μ.prod ν) (((discarded₁ ×ˢ univ) ∪ (univ ×ˢ discarded₂)) ∪ (Γ\good)) badL
    have hu₄ := measure_union_le (μ:=μ.prod ν) ((((discarded₁ ×ˢ univ) ∪ (univ ×ˢ discarded₂)) ∪ (Γ\good)) ∪ badL) badR
    have hsum : (μ.prod ν) bad ≤ μ discarded₁ + ν discarded₂ + (μ.prod ν) (Γ\good) +
        ENNReal.ofReal ((Fintype.card κ:ℝ)*(K:ℝ)*((2:ℝ)^N)^(-sig)) +
        ENNReal.ofReal ((Fintype.card ι:ℝ)*(K:ℝ)*((2:ℝ)^N)^(-sig)) := by
      have hh := hu₄.trans (add_le_add (hu₃.trans (add_le_add (hu₂.trans (add_le_add_left hu₁ _)) hbadL)) hbadR)
      simpa only [Measure.prod_prod,measure_univ,mul_one,one_mul,bad] using hh
    apply hsum.trans_eq
    rw [add_assoc (μ discarded₁+ν discarded₂+(μ.prod ν) (Γ\good)),←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    push_cast
    dsimp [K]
    push_cast
    ring
  have hone : ∀ z∈Γ, z∉bad → assemblyTheta F G kap C beta z=1 := by
    intro z hz hnot
    have hx : z.1∈⋃ i,F.domain i := by
      by_contra hx
      apply hnot
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hx,mem_univ _⟩)))
    have hy : z.2∈⋃ j,G.domain j := by
      by_contra hy
      apply hnot
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨mem_univ _,hy⟩)))
    have hzg : z∈good := by
      by_contra hg
      exact hnot (Or.inl (Or.inl (Or.inr ⟨hz,hg⟩)))
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    rw [assemblyTheta_at F G kap C beta hi hj]
    apply assemblyPairMask_one _ _ _ (hroot hz)
    · intro b hb
      by_contra hfail
      apply hnot
      apply Or.inl ∘ Or.inr
      exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,mem_iUnion₂.mpr ⟨b,hb,hi,hzg,hfail⟩⟩⟩
    · intro b hb
      by_contra hfail
      apply hnot
      apply Or.inr
      exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨i,mem_iUnion₂.mpr ⟨b,hb,hj,hzg,hfail⟩⟩⟩
  have hbound : ∀ z∈Γ, (dist z.1 z.2)^(-(n:ℝ)/2)≤δ^(-(n:ℝ)/2) := by
    intro z hz
    apply Real.rpow_le_rpow_of_nonpos hδ (hsep z hz)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num)
  have hdef := _root_.OAI.CurrentFalconer.AssemblyRetention.masked_pushforward_deficit
    (μ.prod ν) (fun z => dist z.1 z.2) (by fun_prop) Γ bad hΓ hmbad
    (fun z => (dist z.1 z.2)^(-(n:ℝ)/2)) (assemblyTheta F G kap C beta)
    ((continuous_fst.dist continuous_snd).measurable.pow_const _)
    (assemblyTheta_measurable F G kap C beta)
    (fun _ => Real.rpow_nonneg dist_nonneg _)
    (assemblyTheta_bounds F G kap C beta) (δ^(-(n:ℝ)/2)) (Real.rpow_nonneg hδ.le _) hbound hone
  have he : _root_.OAI.CurrentFalconer.AssemblyLimit.filteredDistanceMeasure μ ν Γ =
      ((μ.prod ν).withDensity (fun z => ENNReal.ofReal
        ((dist z.1 z.2)^(-(n:ℝ)/2)*Γ.indicator (fun _ => (1:ℝ)) z))).map (fun z => dist z.1 z.2) := by
    simp only [_root_.OAI.CurrentFalconer.AssemblyLimit.filteredDistanceMeasure,
      _root_.OAI.CurrentFalconer.AssemblyLimit.pairWeight,_root_.OAI.CurrentFalconer.AssemblyLimit.pairDistance,
      Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    rfl
  rw [he]
  exact ⟨hdef.1,hdef.2.trans (mul_le_mul_right hmass _)⟩

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
