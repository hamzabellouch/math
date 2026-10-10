import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularHCongr
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFixedAngularBudget

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Attempt4Near Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}

lemma graph_children_H_split
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {a p : ℕ} (hap : a ≤ p) {X Y : CellPath d} (hX : X ∈ dyadicPaths a) (hY : Y ∈ dyadicPaths a)
    {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B) (hc : GraphSymbolJet c m s B)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0) (v : ℝ) (Ψ : ℝ → ℝ) :
    sourceAngularHND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) a v Ψ
      (fun z => sourceAngularTransformND ρ (treeCell X) Ma₁ b z.1 z.2)
      (fun z => sourceAngularTransformND κ (treeCell Y) Ma₂ c z.1 z.2) =
    sourceAngularHND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) a v Ψ
      (fun z => (Mp₁/Ma₁) • ∑ P ∈ graphChildren ρ a p X, sourceAngularTransformND ρ (treeCell P) Mp₁ b z.1 z.2)
      (fun z => (Mp₂/Ma₂) • ∑ Q ∈ graphChildren κ a p Y, sourceAngularTransformND κ (treeCell Q) Mp₂ c z.1 z.2) := by
  apply sourceAngularHND_congr
  · intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact graph_children_transform_split ρ hap hX hb hMp₁ r w hw
  · intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact graph_children_transform_split κ hap hY hc hMp₂ r w hw

lemma graph_children_HF_split
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {a p : ℕ} (hap : a ≤ p) {X Y : CellPath d} (hX : X ∈ dyadicPaths a) (hY : Y ∈ dyadicPaths a)
    {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B) (hc : GraphSymbolJet c m s B)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (v : ℝ) (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ) :
    sourceAngularHFND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) a v Ψ ψ
      (fun z => sourceAngularTransformND ρ (treeCell X) Ma₁ b z.1 z.2)
      (fun z => sourceAngularTransformND κ (treeCell Y) Ma₂ c z.1 z.2) =
    sourceAngularHFND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) a v Ψ ψ
      (fun z => (Mp₁/Ma₁) • ∑ P ∈ graphChildren ρ a p X, sourceAngularTransformND ρ (treeCell P) Mp₁ b z.1 z.2)
      (fun z => (Mp₂/Ma₂) • ∑ Q ∈ graphChildren κ a p Y, sourceAngularTransformND κ (treeCell Q) Mp₂ c z.1 z.2) := by
  apply sourceAngularHFND_congr
  · intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact graph_children_transform_split ρ hap hX hb hMp₁ r w hw
  · intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact graph_children_transform_split κ hap hY hc hMp₂ r w hw

lemma graph_direct_product_identity (z : ℂ) (e₁ e₂ : ℝ) (u u' v v' : ℂ) :
    z*((e₁:ℂ)*u*conj u')*((e₂:ℂ)*v*conj v') =
      z*((e₁:ℂ)*(e₂:ℂ))*((u*v)*conj (u'*v')) := by
  simp only [map_mul]
  ring

lemma graph_crossed_product_identity (z : ℂ) (e₁ e₂ : ℝ) (s t u u' v v' : ℂ) :
    z*((e₁:ℂ)*s*u*conj v')*((e₂:ℂ)*conj t*v*conj u') =
      z*((e₁:ℂ)*(e₂:ℂ))*(((s*u)*v)*conj ((t*u')*v')) := by
  simp only [map_mul]
  ring

lemma graph_direct_cell_integrable
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (M₁ M₂ : ℝ) {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B) (hc : GraphSymbolJet c m s B)
    {Ψ : ℝ → ℝ} (v : ℝ) (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (δ : ℝ) (k₁ k₂ : Fin d → ℤ) (row col : CellPath d × CellPath d) :
    Integrable (fun q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))) =>
    (Ψ (q.1/(2:ℝ)^v):ℂ)*((tensorCapND δ k₁ q.2.1*tensorCapND δ k₂ q.2.2):ℂ)*
      ((sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2.1 *
        sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2.2)*
       conj (sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2.1 *
        sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2.2)))
      (volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))))) := by
  have h := graph_angular_four_integrable (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)))
    hΨ.ofReal (fun w => (tensorCapND δ k₁ w:ℂ)) (fun w => (tensorCapND δ k₂ w:ℂ))
    (Complex.ofRealCLM.continuous.measurable.comp (tensorCapND_contDiff δ k₁).continuous.measurable)
    (Complex.ofRealCLM.continuous.measurable.comp (tensorCapND_contDiff δ k₂).continuous.measurable)
    (fun z => sourceAngularTransformND ρ (treeCell row.1) M₁ b z.1 z.2)
    (fun z => sourceAngularTransformND ρ (treeCell col.1) M₁ b z.1 z.2)
    (fun z => sourceAngularTransformND κ (treeCell row.2) M₂ c z.1 z.2)
    (fun z => sourceAngularTransformND κ (treeCell col.2) M₂ c z.1 z.2)
    (sourceAngularTransformND_measurable _ _ _ hb.measurable)
    (sourceAngularTransformND_measurable _ _ _ hb.measurable)
    (sourceAngularTransformND_measurable _ _ _ hc.measurable)
    (sourceAngularTransformND_measurable _ _ _ hc.measurable)
    (P₁:=1) (P₂:=1)
    (B₁:=|M₁⁻¹| *ρ.real (treeCell row.1)*B) (B₂:=|M₁⁻¹| *ρ.real (treeCell col.1)*B)
    (B₃:=|M₂⁻¹| *κ.real (treeCell row.2)*B) (B₄:=|M₂⁻¹| *κ.real (treeCell col.2)*B)
    (by norm_num) (by norm_num) (by positivity [hb.nonneg]) (by positivity [hb.nonneg])
    (by positivity [hc.nonneg]) (by positivity [hc.nonneg]) ?_
  · apply h.congr
    filter_upwards with q
    exact graph_direct_product_identity _ _ _ _ _ _ _
  · filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    refine ⟨?_,?_,fun r => ⟨?_,?_,?_,?_⟩⟩
    · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tensorCapND_nonneg _ _ _)] using tensorCapND_le_one δ k₁ w
    · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tensorCapND_nonneg _ _ _)] using tensorCapND_le_one δ k₂ w
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb.norm_le x w hw)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb.norm_le x w hw)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hc.norm_le x w hw)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hc.norm_le x w hw)
lemma graph_crossed_cell_integrable
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (M₁ M₂ : ℝ) {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B) (hc : GraphSymbolJet c m s B)
    {Ψ : ℝ → ℝ} (v : ℝ) (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ) (hmψ : Measurable ψ)
    {P : ℝ} (hP : 0 ≤ P) (hψ : ∀ w, ‖w‖=1 → ‖ψ w‖ ≤ P)
    (δ : ℝ) (k₁ k₂ : Fin d → ℤ) (row col : CellPath d × CellPath d) :
    Integrable (fun q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))) =>
    (Ψ (q.1/(2:ℝ)^v):ℂ)*((tensorCapND δ k₁ q.2.1*tensorCapND δ k₂ q.2.2):ℂ)*
      (((ψ q.2.1*sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2.1) *
        sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2.2)*
       conj ((ψ q.2.2*sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2.2) *
        sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2.1)))
      (volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))))) := by
  have h := graph_angular_four_integrable (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)))
    hΨ.ofReal (fun w => (tensorCapND δ k₁ w:ℂ)*ψ w) (fun w => (tensorCapND δ k₂ w:ℂ)*conj (ψ w))
    ((Complex.ofRealCLM.continuous.measurable.comp (tensorCapND_contDiff δ k₁).continuous.measurable).mul hmψ)
    ((Complex.ofRealCLM.continuous.measurable.comp (tensorCapND_contDiff δ k₂).continuous.measurable).mul (Complex.continuous_conj.measurable.comp hmψ))
    (fun z => sourceAngularTransformND ρ (treeCell row.1) M₁ b z.1 z.2)
    (fun z => sourceAngularTransformND κ (treeCell col.2) M₂ c z.1 z.2)
    (fun z => sourceAngularTransformND κ (treeCell row.2) M₂ c z.1 z.2)
    (fun z => sourceAngularTransformND ρ (treeCell col.1) M₁ b z.1 z.2)
    (sourceAngularTransformND_measurable _ _ _ hb.measurable)
    (sourceAngularTransformND_measurable _ _ _ hc.measurable)
    (sourceAngularTransformND_measurable _ _ _ hc.measurable)
    (sourceAngularTransformND_measurable _ _ _ hb.measurable)
    (P₁:=P) (P₂:=P)
    (B₁:=|M₁⁻¹| *ρ.real (treeCell row.1)*B) (B₂:=|M₂⁻¹| *κ.real (treeCell col.2)*B)
    (B₃:=|M₂⁻¹| *κ.real (treeCell row.2)*B) (B₄:=|M₁⁻¹| *ρ.real (treeCell col.1)*B)
    hP hP (by positivity [hb.nonneg]) (by positivity [hc.nonneg])
    (by positivity [hc.nonneg]) (by positivity [hb.nonneg]) ?_
  · apply h.congr
    filter_upwards with q
    exact graph_crossed_product_identity _ _ _ _ _ _ _ _ _
  · filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    refine ⟨?_,?_,fun r => ⟨?_,?_,?_,?_⟩⟩
    · simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tensorCapND_nonneg _ _ _),one_mul] using
        mul_le_mul (tensorCapND_le_one δ k₁ w) (hψ w hw) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    · simpa only [norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tensorCapND_nonneg _ _ _),one_mul] using
        mul_le_mul (tensorCapND_le_one δ k₂ w) (hψ w hw) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb.norm_le x w hw)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hc.norm_le x w hw)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hc.norm_le x w hw)
    · exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb.norm_le x w hw)
end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}

attribute [local instance] Classical.propDecidable

lemma graphCapScale_pos {N a p : ℕ} {c₀ sig : ℝ} (hc₀ : 0 < c₀) :
    0 < graphCapScale N a p c₀ sig := lt_min hc₀ (by positivity)

lemma graphCapScale_eq (N a p : ℕ) (c₀ sig : ℝ) :
    graphCapScale N a p c₀ sig = min c₀ (((2:ℝ)^((p:ℝ)-a))⁻¹*((2:ℝ)^N)^(10*sig)) := by
  simp only [graphCapScale,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]

lemma graph_pair_partition_ae {N a p : ℕ} {c₀ sig : ℝ}
    (hc₀ : 0 < c₀) (hcsmall : (d+1:ℝ)*c₀ ≤ 1/2) :
    let δ := graphCapScale N a p c₀ sig
    ∀ᵐ z ∂(canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
      (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))),
      (∀ k ∈ (sphereCapGridND d δ).product (sphereCapGridND d δ),
        0 ≤ tensorCapND δ k.1 z.1*tensorCapND δ k.2 z.2) ∧
      ∑ k ∈ (sphereCapGridND d δ).product (sphereCapGridND d δ),
        tensorCapND δ k.1 z.1*tensorCapND δ k.2 z.2=1 := by
  dsimp only
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (canonicalSphereMeasureND_ae_norm (d:=d)),
    Measure.quasiMeasurePreserving_snd.ae (canonicalSphereMeasureND_ae_norm (d:=d))] with z hz₁ hz₂
  exact sphereCap_pair_partition (graphCapScale_pos hc₀)
    ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans hcsmall) z ⟨hz₁,hz₂⟩

theorem source_graph_cap_degrees {sig c₀ : ℝ} (hsig : 0 < sig) (hc₀ : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (ρ₁ ρ₂ : Measure (EuclideanSpace ℝ (Fin d))) (A₁ A₂ : ℕ → ℝ)
      (C : ℝ) (J i₁ i₂ a g₁ g₂ p : ℕ) (X Y : CellPath d) (A B : Finset (CellPath d))
      (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ),
    a ≤ g₁ → a ≤ g₂ → g₁ ≤ p → g₂ ≤ p →
    (g₁:ℝ) ≤ (a:ℝ)+2*sig*N → (g₂:ℝ) ≤ (a:ℝ)+2*sig*N →
    0 < J → i₁ ≤ J → i₂ ≤ J →
    ImposesParallelTest ρ₁ g₁ p (testWidth N J i₁ p sig)
      (((2:ℝ)^N)^(height A₁ g₁ p+C*sig)) b →
    ImposesParallelTest ρ₂ g₂ p (testWidth N J i₂ p sig)
      (((2:ℝ)^N)^(height A₂ g₂ p+C*sig)) c →
    let δ := graphCapScale N a p c₀ sig
    let τ := graphTolerance N p sig
    let D := ((2:ℝ)^N)^(min (height A₁ a p) (height A₂ a p)+(C+32*(d:ℝ)+1)*sig)
    ∀ k ∈ (sphereCapGridND d δ).product (sphereCapGridND d δ),
    let Sv := eligibleCells ρ₁ a p X (tensorCapND δ k.1) b
    let Sw := eligibleCells ρ₁ a p X (tensorCapND δ k.2) b
    let Tv := eligibleCells ρ₂ a p Y (tensorCapND δ k.1) c
    let Tw := eligibleCells ρ₂ a p Y (tensorCapND δ k.2) c
    let v := sphereCapCenterND δ k.1
    let w := sphereCapCenterND δ k.2
    (∀ row,
      (((A.product B).filter (retainedHGraph Sv Tw v w τ row)).card : ℝ) ≤ D ∧
      (((A.product B).filter (retainedHFGraph Sv Sw Tv Tw v w τ row)).card : ℝ) ≤ D) ∧
    (∀ col,
      (((A.product B).filter (fun row => retainedHGraph Sv Tw v w τ row col)).card : ℝ) ≤ D ∧
      (((A.product B).filter (fun row => retainedHFGraph Sv Sw Tv Tw v w τ row col)).card : ℝ) ≤ D) := by
  obtain ⟨N₀,hN₀⟩ := source_graph_degrees (d:=d) hsig hc₀.le (by positivity : (0:ℝ) ≤ 2*(d+1:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN ρ₁ ρ₂ A₁ A₂ C J i₁ i₂ a g₁ g₂ p X Y A B b c hag₁ hag₂ hg₁ hg₂ hga₁ hga₂ hJ hi₁ hi₂ ht₁ ht₂ δ τ D k hk
  have hk' := Finset.mem_product.mp hk
  apply hN₀ N hN ρ₁ ρ₂ A₁ A₂ C J i₁ i₂ a g₁ g₂ p X Y A B
    (tensorCapND δ k.1) (tensorCapND δ k.2) b c
    (sphereCapCenterND δ k.1) (sphereCapCenterND δ k.2)
    hag₁ hag₂ hg₁ hg₂ hga₁ hga₂ hJ hi₁ hi₂ (sphereCapCenterND_norm hk'.1) (sphereCapCenterND_norm hk'.2)
    ?_ ?_ ht₁ ht₂
  · intro w hw hn
    rw [dist_comm]
    exact sphereCapCenterND_dist (graphCapScale_pos hc₀) hk'.1 hw (subset_tsupport _ hn)
  · intro w hw hn
    rw [dist_comm]
    exact sphereCapCenterND_dist (graphCapScale_pos hc₀) hk'.2 hw (subset_tsupport _ hn)

lemma graph_profile_ratio {N : ℕ} (_hN : 0 < N) (m : ℝ → ℝ) (a p : ℕ) :
    ((2:ℝ)^N)^(-m p)/((2:ℝ)^N)^(-m a) =
      ((2:ℝ)^N)^(-((adjustedProfile (d:=d) m N p-adjustedProfile (d:=d) m N a)+
        (d:ℝ)/2*((p:ℝ)-a)/(N:ℝ))) := by
  rw [←Real.rpow_sub (by positivity : (0:ℝ) < 2^N)]
  congr 1
  unfold adjustedProfile
  ring

lemma graph_profile_label_exponent (m₁ m₂ : ℝ → ℝ) (N a p : ℕ) (e : ℝ) :
    (m₁ p-m₁ a)+(m₂ p-m₂ a)+4*e =
      (adjustedProfile (d:=d) m₁ N p-adjustedProfile (d:=d) m₁ N a)+
      (adjustedProfile (d:=d) m₂ N p-adjustedProfile (d:=d) m₂ N a)+
      (d:ℝ)*((p:ℝ)-a)/(N:ℝ)+4*e := by
  unfold adjustedProfile
  ring

lemma graphChildren_card_crude (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {N a p : ℕ} (hp : p ≤ N) (X : CellPath d) :
    ((graphChildren ρ a p X).card:ℝ) ≤ ((2:ℝ)^N)^d := by
  have hsub : graphChildren ρ a p X ⊆ dyadicPaths p := by
    intro P hP
    exact (mem_dyadicPaths _ _).mpr (graphChildren_length hP)
  have hc := (Finset.card_le_card hsub).trans (dyadicPaths_card_le p)
  have hmono : (2^d)^p ≤ (2^d)^N := Nat.pow_le_pow_right (by positivity) hp
  have h := (Nat.cast_le (α:=ℝ)).mpr (hc.trans hmono)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,pow_right_comm] using h

lemma graphCellLaw_mass_crude (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ]
    {R m : ℝ} (hR : 1 ≤ R) (hm : m ≤ d) (P : Set (EuclideanSpace ℝ (Fin d))) :
    (graphCellLaw ρ P (R^(-m))).real univ ≤ R^d := by
  rw [graphCellLaw_mass _ _ (by positivity)]
  have hinv : (R^(-m))⁻¹=R^m := by rw [Real.rpow_neg (by linarith : 0 ≤ R),inv_inv]
  rw [hinv]
  calc
    _ ≤ R^m*1 := mul_le_mul_of_nonneg_left (measureReal_le_one) (by positivity)
    _ ≤ R^d := by simpa only [mul_one,Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hR hm

lemma graph_profile_ratio_crude {R ma mp : ℝ} (hR : 1 ≤ R) (ha : ma ≤ d) (hp : 0 ≤ mp) :
    0 ≤ R^(-mp)/R^(-ma) ∧ R^(-mp)/R^(-ma) ≤ R^d := by
  constructor
  · positivity
  rw [←Real.rpow_sub (by linarith : 0 < R)]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hR (show -mp- -ma ≤ (d:ℝ) by linarith)

end CurrentFalconer.TreeND
end
end

end OAI
