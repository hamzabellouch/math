import OAI.MeasureTheory.Falconer.Fourier.InverseJetState

namespace OAI

/-! # Actual recursive symbols produced by the inverse

The old descriptor list and spatial multiplier survive unchanged. The
angular multiplier is the geometric inverse coefficient times the newly
differentiated old multiplier, with a fixed normalization. The new finite
smoothness budget is explicit.
-/

namespace Falconer
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace MaskJetExpansion
variable {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem seed_inverse_right_order (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) :
    (∑ i, ((((seed k).inverse m j).term a).jet (.inr i)).order) ≤
      (∑ i, (k (.inr i)).order)+2*j := by
  have htotal := seededJetSeparation_added_order m j k a
  change
    (∑ i, (((((seed k).inverse m j).term a).jet (.inl i)).order-(k (.inl i)).order)) +
      (∑ i, (((((seed k).inverse m j).term a).jet (.inr i)).order-(k (.inr i)).order)) ≤ 2*j
    at htotal
  have hsum :
      (∑ i, (((((seed k).inverse m j).term a).jet (.inr i)).order-(k (.inr i)).order)) +
        (∑ i, (k (.inr i)).order) =
        ∑ i, ((((seed k).inverse m j).term a).jet (.inr i)).order := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel ((seed_ordersExtend k).inverse j a (.inr i))
  omega

end MaskJetExpansion

namespace DescriptorJetSymbol
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

noncomputable def inverseRightJets (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ G then
    (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
      (.inr (.inr ⟨b,hb⟩)) else MaskJetIndex.zero (m+3)

theorem inverseRightJets_order (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    (∑ b ∈ G, (f.inverseRightJets g j a b).order) ≤ KR+2*j := by
  let k := descriptorInverseSeed f g
  let T := (MaskJetExpansion.seed k).inverse m j
  have hright := MaskJetExpansion.seed_inverse_right_order m j k a
  have hinitial : (∑ i : DescriptorInverseLabel G, (k (.inr i)).order) =
      ∑ b ∈ G, (g.jet b).order := by
    rw [Fintype.sum_sum_type]
    simp only [k,descriptorInverseSeed,Sum.elim_inl,Sum.elim_inr,MaskJetIndex.zero,
      Fintype.sum_unique,zero_add]
    exact Finset.sum_coe_sort G (fun b => (g.jet b).order)
  have hout : (∑ b ∈ G, (f.inverseRightJets g j a b).order) =
      ∑ b : {b // b ∈ G}, ((T.term a).jet (.inr (.inr b))).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [inverseRightJets,dite_eq_left b.property]
    rfl
  rw [hinitial] at hright
  rw [hout]
  have hpartial : (∑ b : {b // b ∈ G}, ((T.term a).jet (.inr (.inr b))).order) ≤
      ∑ i : DescriptorInverseLabel G, ((T.term a).jet (.inr i)).order := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique]
    omega
  exact hpartial.trans (hright.trans (Nat.add_le_add_right g.order_le (2*j)))

end DescriptorJetSymbol

/-- The left endpoint factor of each actual inverse term belongs to the
factorized class. The old multiplier needs `R+2*j` available derivatives. -/
theorem exists_inverse_left_symbol (m j R : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (KL KR L : ℕ) (F G : Finset PolicyDescriptor) (D : ℝ)
      (f : DescriptorJetSymbol (m+1) KL L F D)
      (g : DescriptorJetSymbol (m+1) KR L G D),
      1 ≤ D → R+2*j ≤ L →
      ∀ a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index,
      ∃ u : DescriptorJetSymbol (m+1) (KL+2*j) R F D,
        u.jet = f.inverseLeftJets g j a ∧ u.spatial = f.spatial ∧
        u.angular = normalizedAngular A
          (fun z => (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).coefficient z *
            ((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
              (.inl (.inl ()))).scaledValue D⁻¹ f.angular z) := by
  obtain ⟨A,hA,hnormalize⟩ := inverse_angular_symbol m j R
  refine ⟨A,hA,?_⟩
  intro KL KR L F G D f g hD hL a
  let k := descriptorInverseSeed f g
  let p := (((MaskJetExpansion.seed k).inverse m j).term a).jet (.inl (.inl ()))
  have hp : p.order ≤ 2*j := by
    have h := MaskJetExpansion.seed_inverse_single_order m j k a (.inl (.inl ()))
    simpa only [p,k,descriptorInverseSeed,Sum.elim_inl,MaskJetIndex.zero,Nat.zero_add] using h
  have hbudget := hnormalize (DescriptorInverseLabel F ⊕ DescriptorInverseLabel G)
    k a p L f.angular f.angular_smooth D hD (by omega) f.angular_derivative
  rcases hbudget with ⟨hsmooth,hderivative,hcontrol⟩
  refine ⟨{
    jet := f.inverseLeftJets g j a
    order_le := f.inverseLeftJets_order g j a
    angular := normalizedAngular A (fun z =>
      (((MaskJetExpansion.seed k).inverse m j).term a).coefficient z *
        p.scaledValue D⁻¹ f.angular z)
    angular_smooth := hsmooth
    angular_derivative := hderivative
    angular_control := hcontrol
    spatial := f.spatial
    spatial_measurable := f.spatial_measurable
    spatial_bound := f.spatial_bound },rfl,rfl,rfl⟩

/-- The right endpoint retains its own original descriptors and spatial
multiplier. Its angular factor has no geometric coefficient. -/
theorem exists_inverse_right_symbol (m j R : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (KL KR L : ℕ) (F G : Finset PolicyDescriptor) (D : ℝ)
      (f : DescriptorJetSymbol (m+1) KL L F D)
      (g : DescriptorJetSymbol (m+1) KR L G D),
      1 ≤ D → R+2*j ≤ L →
      ∀ a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index,
      ∃ u : DescriptorJetSymbol (m+1) (KR+2*j) R G D,
        u.jet = f.inverseRightJets g j a ∧ u.spatial = g.spatial ∧
        u.angular = normalizedAngular A
          (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
              (.inr (.inl ()))).scaledValue D⁻¹ g.angular) := by
  obtain ⟨A,hA,hnormalize⟩ := angular_jet_symbol (m+1) R
  refine ⟨A,hA,?_⟩
  intro KL KR L F G D f g hD hL a
  let k := descriptorInverseSeed f g
  let p := (((MaskJetExpansion.seed k).inverse m j).term a).jet (.inr (.inl ()))
  have hp : p.order ≤ 2*j := by
    have h := MaskJetExpansion.seed_inverse_single_order m j k a (.inr (.inl ()))
    simpa only [p,k,descriptorInverseSeed,Sum.elim_inl,Sum.elim_inr,MaskJetIndex.zero,
      Nat.zero_add] using h
  have hbudget := hnormalize L p g.angular g.angular_smooth D hD (by omega)
    g.angular_derivative
  rcases hbudget with ⟨hsmooth,hderivative,hcontrol⟩
  refine ⟨{
    jet := f.inverseRightJets g j a
    order_le := f.inverseRightJets_order g j a
    angular := normalizedAngular A (p.scaledValue D⁻¹ g.angular)
    angular_smooth := hsmooth
    angular_derivative := hderivative
    angular_control := hcontrol
    spatial := g.spatial
    spatial_measurable := g.spatial_measurable
    spatial_bound := g.spatial_bound },rfl,rfl,rfl⟩

end Falconer

end OAI
