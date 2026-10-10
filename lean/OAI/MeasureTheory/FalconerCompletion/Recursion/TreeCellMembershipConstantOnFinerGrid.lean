import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.ResidualPairSourceSymbolEqScalarPair

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff ENNReal Topology Classical
variable {n : ℕ}

lemma treeCell_membership_constant_on_finer_grid
    {P : CellPath (n+1)} {h : ℕ} (hP : P.length≤h) (X : Fin (n+1) → ℤ)
    {x y : EuclideanSpace ℝ (Fin (n+1))}
    (hx : x∈CurrentFalconer.ambientGridCell h X)
    (hy : y∈CurrentFalconer.ambientGridCell h X) : x∈treeCell P ↔ y∈treeCell P := by
  have hs := CurrentFalconer.ambientGridCell_subset_ancestor hP X
  have one {u v : EuclideanSpace ℝ (Fin (n+1))}
      (hu : u∈CurrentFalconer.ambientGridCell h X)
      (hv : v∈CurrentFalconer.ambientGridCell h X) (huP : u∈treeCell P) : v∈treeCell P := by
    have he : (fun i => X i/(2:ℤ)^(h-P.length))=(fun i => (pathIndex P i:ℤ)) := by
      by_contra hne
      exact Set.disjoint_left.mp (CurrentFalconer.ambientGridCell_disjoint hne) (hs hu) huP
    have hh := hs hv
    rw [he] at hh
    exact hh
  exact ⟨one hx hy,one hy hx⟩

lemma actualEndpointSmooth_grid_reached
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) {h : ℕ} (ha : descriptorAnchor b≤h)
    (X : Fin (n+1) → ℤ) {x y : EuclideanSpace ℝ (Fin (n+1))}
    (hx : x∈CurrentFalconer.ambientGridCell h X) (hy : y∈CurrentFalconer.ambientGridCell h X) :
    actualEndpointSmooth ρ m N sig C J i b x=actualEndpointSmooth ρ m N sig C J i b y := by
  have he (P : CellPath (n+1)) (hP : P∈dyadicPaths (descriptorAnchor b)) :
      x∈treeCell P ↔ y∈treeCell P :=
    treeCell_membership_constant_on_finer_grid ((mem_dyadicPaths _ _).mp hP ▸ ha) X hx hy
  by_cases ex : ∃ P∈dyadicPaths (descriptorAnchor b), x∈treeCell P
  · obtain ⟨P,hP,hxP⟩ := ex
    rw [actualEndpointSmooth_of_mem ρ m N sig C J i b hP hxP,
      actualEndpointSmooth_of_mem ρ m N sig C J i b hP ((he P hP).mp hxP)]
  · have hx0 : ∀ P∈dyadicPaths (descriptorAnchor b), x∉treeCell P := by
      intro P hP hxP
      exact ex ⟨P,hP,hxP⟩
    rw [actualEndpointSmooth_of_absent ρ m N sig C J i b hx0,
      actualEndpointSmooth_of_absent ρ m N sig C J i b (fun P hP hyP => hx0 P hP ((he P hP).mpr hyP))]

lemma actualAngularProduct_grid_reached
    (D : Finset PolicyDescriptor)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) {h : ℕ} (ha : ∀ b∈D, descriptorAnchor b≤h)
    (X : Fin (n+1) → ℤ) {x y : EuclideanSpace ℝ (Fin (n+1))}
    (hx : x∈CurrentFalconer.ambientGridCell h X) (hy : y∈CurrentFalconer.ambientGridCell h X) :
    actualAngularProduct D id L ρ m N sig C J i x=actualAngularProduct D id L ρ m N sig C J i y := by
  apply Subtype.ext
  funext w
  apply Finset.prod_congr rfl
  intro b hb
  have he : actualEndpointAngular (L b) ρ m N sig C J i b x=actualEndpointAngular (L b) ρ m N sig C J i b y := by
    unfold actualEndpointAngular
    rw [actualEndpointSmooth_grid_reached ρ m N sig C J i b (ha b hb) X hx hy]
  exact congrArg (fun f : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) => f.1 w) he

noncomputable def newlyReachedDescriptorList (A : ℕ → ℝ) (N q a t p h : ℕ) : Finset PolicyDescriptor :=
  (unreachedDescriptorList A N q a t p).filter (fun b => descriptorAnchor b≤h)

lemma actualResidualAngular_step_factorization
    (A : ℕ → ℝ) (N q a t p h : ℕ) (hph : p≤h)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1))) :
    actualResidualAngular A N q a t p L ρ m sig C J i x =
      smoothMulND (actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L ρ m N sig C J i x)
        (actualResidualAngular A N q a t h L ρ m sig C J i x) := by
  have hcomp : (unreachedDescriptorList A N q a t p).filter (fun b => ¬descriptorAnchor b≤h)=
      unreachedDescriptorList A N q a t h := by
    ext b
    simp only [unreachedDescriptorList,Finset.mem_filter,not_le]
    constructor
    · rintro ⟨⟨hb, _⟩, hbh⟩
      exact ⟨hb,hbh⟩
    · rintro ⟨hb,hbh⟩
      exact ⟨⟨hb,lt_of_le_of_lt hph hbh⟩,hbh⟩
  apply Subtype.ext
  funext w
  have he := (Finset.prod_filter_mul_prod_filter_not
    (unreachedDescriptorList A N q a t p) (fun b => descriptorAnchor b≤h)
    (fun b => (actualEndpointAngular (L b) ρ m N sig C J i b x).1 w)).symm
  rw [hcomp] at he
  exact he

lemma actualResidualSourceSymbol_grid_factorization
    (A : ℕ → ℝ) (N q a t p h : ℕ) (hph : p≤h)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (X : Fin (n+1) → ℤ) {x : EuclideanSpace ℝ (Fin (n+1))}
    (hx : x∈CurrentFalconer.ambientGridCell h X) (w : EuclideanSpace ℝ (Fin (n+1))) :
    (actualResidualSourceSymbol A N q a t p L ρ m sig C J i f Q x).1 w =
      (actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L ρ m N sig C J i
        (CurrentFalconer.ambientGridCenter h X)).1 w *
      (actualResidualSourceSymbol A N q a t h L ρ m sig C J i f Q x).1 w := by
  have he := actualResidualAngular_step_factorization A N q a t p h hph L ρ m sig C J i x
  have hc := actualAngularProduct_grid_reached (newlyReachedDescriptorList A N q a t p h)
    L ρ m N sig C J i (fun b hb => (Finset.mem_filter.mp hb).2) X hx
      (CurrentFalconer.ambientGridCenter_mem h X)
  change f x*(Q.1 w*(actualResidualAngular A N q a t p L ρ m sig C J i x).1 w)=_
  rw [he]
  change f x*(Q.1 w*((actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L ρ m N sig C J i x).1 w * _))=_
  rw [hc]
  change f x*(Q.1 w*(_*_))=_*(f x*(Q.1 w*_))
  dsimp only [actualResidualAngular]
  ring

lemma actualResidualTransform_grid_factorization
    (A : ℕ → ℝ) (N q a t p h : ℕ) (hph : p≤h)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (X : Fin (n+1) → ℤ) (M r : ℝ) (w : EuclideanSpace ℝ (Fin (n+1))) :
    sourceAngularTransformND ρ (CurrentFalconer.ambientGridCell h X) M
      (fun x => (actualResidualSourceSymbol A N q a t p L ρ m sig C J i f Q x).1) r w =
    (actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L ρ m N sig C J i
      (CurrentFalconer.ambientGridCenter h X)).1 w *
    sourceAngularTransformND ρ (CurrentFalconer.ambientGridCell h X) M
      (fun x => (actualResidualSourceSymbol A N q a t h L ρ m sig C J i f Q x).1) r w := by
  unfold sourceAngularTransformND
  rw [show (∫ x in CurrentFalconer.ambientGridCell h X, spherePlaneWaveND r x w*(actualResidualSourceSymbol A N q a t p L ρ m sig C J i f Q x).1 w ∂ρ) =
      ∫ x in CurrentFalconer.ambientGridCell h X,
        (actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L ρ m N sig C J i (CurrentFalconer.ambientGridCenter h X)).1 w *
          (spherePlaneWaveND r x w*(actualResidualSourceSymbol A N q a t h L ρ m sig C J i f Q x).1 w) ∂ρ by
    apply setIntegral_congr_fun (CurrentFalconer.measurableSet_ambientGridCell h X)
    intro x hx
    dsimp only
    rw [actualResidualSourceSymbol_grid_factorization A N q a t p h hph L ρ m sig C J i f Q X hx w]
    ring]
  rw [integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

lemma uniform_newlyReachedSymbol_bound
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B) (sig : ℝ) (hsig : 0<sig) :
    ∃ D : ℝ, 1≤D ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (A : ℕ → ℝ) (q a t p h : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ),
      (∀ b ∈ policyDescriptorList A N q a t, L b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L b).length ≤ total) →
      ∀ (x w : EuclideanSpace ℝ (Fin (n+1))), ‖w‖=1 →
      ‖(actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L ρ m N sig C J i x).1 w‖ ≤ D^total := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualAngularProduct_derivatives
    (ι:=PolicyDescriptor) W 0 B total 3 hW 8 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,Filter.eventually_ge_atTop 1] with N hDb hN
  intro A q a t p h hq L ρ m C J i hL htotal x w hw
  have hsub : newlyReachedDescriptorList A N q a t p h ⊆ policyDescriptorList A N q a t := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hcard : ((newlyReachedDescriptorList A N q a t p h).card:ℝ)≤8*(N:ℝ)^3 := by
    calc
      _ ≤ ((policyDescriptorList A N q a t).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ _ := actualPolicy_card_bound A hN hq
  have hsum : ∑ b∈newlyReachedDescriptorList A N q a t p h, (L b).length ≤ total :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)).trans htotal
  have hh := hDb (newlyReachedDescriptorList A N q a t p h) id L ρ m C J i
    ((policyDescriptorList A N q a t).sup descriptorLength) hcard
    (fun b hb => hL b (hsub hb)) hsum (fun b hb => Finset.le_sup (f:=descriptorLength) (hsub hb)) x 0 le_rfl w hw
  simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hh

theorem actualResidual_graph_reached_removalND
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B) {sig : ℝ} (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ D : ℝ, 1≤D ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a t p h : ℕ), 0<q → p≤h →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q S : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a t, L₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a t, L₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a t, (L₂ b).length≤total) →
      (∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq) → (∀ w, ‖w‖=1 → ‖S.1 w‖≤Cq) →
      ∀ (X Y : Finset (Fin (n+1) → ℤ)) (hXY : (X.product Y).Nonempty) (M K v : ℝ) (Ψ : ℝ → ℝ),
      Integrable (fun r => Ψ (r/(2:ℝ)^v)) → (∀ r, 0≤Ψ r) →
      Attempt4Near.graphChildMaxND (n+1) (Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) h v Ψ X Y hXY
        (originalCellTransformND ρ h M (fun x => (actualResidualSourceSymbol A N q a t p L₁ ρ m sig C J i f Q x).1))
        (originalCellTransformND κ h K (fun x => (actualResidualSourceSymbol A N q a t p L₂ κ m sig C J i g S x).1)) ≤
      D^(4*total)*
        Attempt4Near.graphChildMaxND (n+1) (Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) h v Ψ X Y hXY
          (originalCellTransformND ρ h M (fun x => (actualResidualSourceSymbol A N q a t h L₁ ρ m sig C J i f Q x).1))
          (originalCellTransformND κ h K (fun x => (actualResidualSourceSymbol A N q a t h L₂ κ m sig C J i g S x).1)) := by
  obtain ⟨D,hD,hDb⟩ := uniform_newlyReachedSymbol_bound W B total hW sig hsig
  obtain ⟨E,hE,hEb⟩ := actual_residual_transform_uniform_package W B total hW hsig Cq hCq
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,hEb] with N hDb hEb
  intro ρ κ hρ hκ A q a t p h hq hph L₁ L₂ m C J i f g Q S hf hg hfb hgb hL₁ hL₂ htotal₁ htotal₂ hQ hS X Y hXY M K v Ψ hΨ hΨpos
  obtain ⟨hbm,hbn,hbt⟩ := hEb ρ A q a t h hq L₁ m C J i f Q hf hfb hL₁ htotal₁ hQ
  obtain ⟨hcm,hcn,hct⟩ := hEb κ A q a t h hq L₂ m C J i g S hg hgb hL₂ htotal₂ hS
  let ψ := fun X w => (actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L₁ ρ m N sig C J i (CurrentFalconer.ambientGridCenter h X)).1 w
  let φ := fun Y w => (actualAngularProduct (newlyReachedDescriptorList A N q a t p h) id L₂ κ m N sig C J i (CurrentFalconer.ambientGridCenter h Y)).1 w
  have hψ (X : Fin (n+1) → ℤ) : ∀ᵐ w ∂Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))), ‖ψ X w‖≤D^total := by
    filter_upwards [Attempt4FullFar.canonicalSphereMeasureND_ae_norm] with w hw
    exact hDb A q a t p h hq L₁ ρ m C J i hL₁ htotal₁ _ w hw
  have hφ (Y : Fin (n+1) → ℤ) : ∀ᵐ w ∂Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))), ‖φ Y w‖≤D^total := by
    filter_upwards [Attempt4FullFar.canonicalSphereMeasureND_ae_norm] with w hw
    exact hDb A q a t p h hq L₂ κ m C J i hL₂ htotal₂ _ w hw
  have hh := Attempt4Near.graphChildMaxND_bounded_factors (n+1)
    (Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) h v X Y hXY
    (originalCellTransformND ρ h M (fun x => (actualResidualSourceSymbol A N q a t h L₁ ρ m sig C J i f Q x).1))
    (originalCellTransformND κ h K (fun x => (actualResidualSourceSymbol A N q a t h L₂ κ m sig C J i g S x).1))
    (fun X _ => (hbt (Attempt4FullFar.ambientGridCell h X) M).1)
    (fun Y _ => (hct (Attempt4FullFar.ambientGridCell h Y) K).1)
    (fun X => |M⁻¹| * (ρ (Attempt4FullFar.ambientGridCell h X)).toReal*E)
    (fun Y => |K⁻¹| * (κ (Attempt4FullFar.ambientGridCell h Y)).toReal*E)
    (fun X _ => (hbt (Attempt4FullFar.ambientGridCell h X) M).2)
    (fun Y _ => (hct (Attempt4FullFar.ambientGridCell h Y) K).2)
    ψ φ (fun X _ => hψ X) (fun Y _ => hφ Y) hΨ hΨpos
  have hpow : (D^total)^2*(D^total)^2=D^(4*total) := by
    rw [← pow_add,← pow_mul]
    congr 1
    omega
  rw [hpow] at hh
  have hUeq : originalCellTransformND ρ h M (fun x => (actualResidualSourceSymbol A N q a t p L₁ ρ m sig C J i f Q x).1) =
      fun X z => ψ X z.2 * originalCellTransformND ρ h M (fun x => (actualResidualSourceSymbol A N q a t h L₁ ρ m sig C J i f Q x).1) X z := by
    funext X z
    exact actualResidualTransform_grid_factorization A N q a t p h hph L₁ ρ m sig C J i f Q X M z.1 z.2
  have hWeq : originalCellTransformND κ h K (fun x => (actualResidualSourceSymbol A N q a t p L₂ κ m sig C J i g S x).1) =
      fun Y z => φ Y z.2 * originalCellTransformND κ h K (fun x => (actualResidualSourceSymbol A N q a t h L₂ κ m sig C J i g S x).1) Y z := by
    funext Y z
    exact actualResidualTransform_grid_factorization A N q a t p h hph L₂ κ m sig C J i g S Y K z.1 z.2
  rw [hUeq,hWeq]
  exact hh

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
