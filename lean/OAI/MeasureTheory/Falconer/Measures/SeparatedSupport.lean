import OAI.MeasureTheory.Falconer.Geometry.SeparationOrder

namespace OAI

/-! # Support bookkeeping for separated angular derivatives

The anchor maps track the point of the original endpoint symbol sampled
by each factor. Differentiation cannot enlarge support, while a chart
substitution pulls it back along its continuous anchor map.
-/

namespace Falconer
open Set
open scoped ContDiff

variable {X Y V W E H : Type*}
  [NormedAddCommGroup V]
  [NormedAddCommGroup W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure SeparationSupport (S : SmoothSeparation X Y E) (B : X → V → ℂ) (C : Y → W → ℂ) where
  leftAnchor : S.index → E → V
  rightAnchor : S.index → E → W
  left_continuous : ∀ i, Continuous (leftAnchor i)
  right_continuous : ∀ i, Continuous (rightAnchor i)
  left_support : ∀ i x, tsupport (S.left i x) ⊆ leftAnchor i ⁻¹' tsupport (B x)
  right_support : ∀ i y, tsupport (S.right i y) ⊆ rightAnchor i ⁻¹' tsupport (C y)

namespace SeparationSupport

def At {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) (z : E) (v : V) (w : W) : Prop :=
  ∀ i, A.leftAnchor i z = v ∧ A.rightAnchor i z = w

noncomputable def product (B : X → E → ℂ) (C : Y → E → ℂ)
    (hB : ∀ x, ContDiff ℝ ∞ (B x)) (hC : ∀ y, ContDiff ℝ ∞ (C y)) :
    SeparationSupport (SmoothSeparation.product B C hB hC) B C where
  leftAnchor := fun _ => id
  rightAnchor := fun _ => id
  left_continuous := fun _ => continuous_id
  right_continuous := fun _ => continuous_id
  left_support := fun _ _ => Subset.rfl
  right_support := fun _ _ => Subset.rfl

noncomputable def mulLeft {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    SeparationSupport (S.mulLeft c hc) B C where
  leftAnchor := A.leftAnchor
  rightAnchor := A.rightAnchor
  left_continuous := A.left_continuous
  right_continuous := A.right_continuous
  left_support := fun i x => tsupport_mul_subset_right.trans (A.left_support i x)
  right_support := A.right_support

noncomputable def pullback {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    SeparationSupport (S.pullback g hg) B C where
  leftAnchor := fun i => A.leftAnchor i ∘ g
  rightAnchor := fun i => A.rightAnchor i ∘ g
  left_continuous := fun i => (A.left_continuous i).comp hg.continuous
  right_continuous := fun i => (A.right_continuous i).comp hg.continuous
  left_support := fun i x => (tsupport_comp_subset_preimage _ hg.continuous).trans
    (preimage_mono (A.left_support i x))
  right_support := fun i y => (tsupport_comp_subset_preimage _ hg.continuous).trans
    (preimage_mono (A.right_support i y))

noncomputable def derivative {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) (v : E) : SeparationSupport (S.derivative v) B C where
  leftAnchor := Sum.elim A.leftAnchor A.leftAnchor
  rightAnchor := Sum.elim A.rightAnchor A.rightAnchor
  left_continuous := by intro i; cases i <;> exact A.left_continuous _
  right_continuous := by intro i; cases i <;> exact A.right_continuous _
  left_support := by
    intro i x
    cases i with
    | inl i => exact (tsupport_fderiv_apply_subset ℝ v).trans (A.left_support i x)
    | inr i => exact A.left_support i x
  right_support := by
    intro i y
    cases i with
    | inl i => exact A.right_support i y
    | inr i => exact (tsupport_fderiv_apply_subset ℝ v).trans (A.right_support i y)

noncomputable def sum {I : Type} [Fintype I] {S : I → SmoothSeparation X Y E}
    {B : X → V → ℂ} {C : Y → W → ℂ} (A : ∀ i, SeparationSupport (S i) B C) :
    SeparationSupport (SmoothSeparation.sum S) B C where
  leftAnchor := fun i => (A i.1).leftAnchor i.2
  rightAnchor := fun i => (A i.1).rightAnchor i.2
  left_continuous := fun i => (A i.1).left_continuous i.2
  right_continuous := fun i => (A i.1).right_continuous i.2
  left_support := fun i => (A i.1).left_support i.2
  right_support := fun i => (A i.1).right_support i.2

noncomputable def laplacian {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) {n : ℕ} (v : Fin n → E) :
    SeparationSupport (S.laplacian v) B C :=
  sum (fun i => (A.derivative (v i)).derivative (v i))

theorem derivative_at {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) {z : E} {v : V} {w : W} (ha : A.At z v w) (u : E) :
    (A.derivative u).At z v w := by
  intro i
  cases i <;> exact ha _

theorem laplacian_at {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) {z : E} {v : V} {w : W} (ha : A.At z v w)
    {n : ℕ} (u : Fin n → E) : (A.laplacian u).At z v w := by
  intro i
  exact ((A.derivative (u i.1)).derivative_at (A.derivative_at ha (u i.1)) (u i.1)) i.2

theorem iteratedLaplacian {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) {n : ℕ} (v : Fin n → E) (j : ℕ) :
    ∃ U : SeparationSupport (S.iteratedLaplacian v j) B C,
      ∀ z a b, A.At z a b → U.At z a b := by
  induction j with
  | zero => exact ⟨A,fun _ _ _ h => h⟩
  | succ j ih =>
    obtain ⟨U,hU⟩ := ih
    rw [SmoothSeparation.iteratedLaplacian,Function.iterate_succ_apply']
    exact ⟨U.laplacian v,fun z a b h => U.laplacian_at (hU z a b h) v⟩

theorem left_mem_of_ne_zero {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) {z : E} {v : V} {w : W} (ha : A.At z v w)
    (i : S.index) (x : X) (hx : S.left i x z ≠ 0) : v ∈ tsupport (B x) := by
  have h := A.left_support i x (subset_closure hx)
  change A.leftAnchor i z ∈ tsupport (B x) at h
  rwa [(ha i).1] at h

theorem right_mem_of_ne_zero {S : SmoothSeparation X Y E} {B : X → V →ℂ} {C : Y → W → ℂ}
    (A : SeparationSupport S B C) {z : E} {v : V} {w : W} (ha : A.At z v w)
    (i : S.index) (y : Y) (hy : S.right i y z ≠ 0) : w ∈ tsupport (C y) := by
  have h := A.right_support i y (subset_closure hy)
  change A.rightAnchor i z ∈ tsupport (C y) at h
  rwa [(ha i).2] at h

theorem stationaryJet {m j : ℕ} {S : SmoothSeparation X Y (Space (m+3))}
    {B : X → Space (m+3) → ℂ} {C : Y → Space (m+3) → ℂ}
    (A : SeparationSupport S B C) :
    ∃ U : SeparationSupport (S.stationaryJet m j) B C,
      ∀ e : Sphere (m+3),
        ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 →
        A.At e e e → U.At e e e := by
  let T := (A.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulLeft
    (SmoothSeparation.stationaryJointDensity m) (SmoothSeparation.stationaryJointDensity_contDiff m)
  obtain ⟨L,hL⟩ := T.iteratedLaplacian (verticalDirections (m+2)) j
  let U := (L.pullback (fun e => (e,(0 : Space (m+2))))
    (contDiff_id.prodMk contDiff_const)).mulLeft
      (SmoothSeparation.stationaryJetMultiplier m j)
      (SmoothSeparation.stationaryJetMultiplier_contDiff m j)
  refine ⟨U,?_⟩
  intro e he hAe
  change L.At (e,0) e e
  apply hL
  change A.At (safeStationaryChart m (e,0)) e e
  rw [safeStationaryChart_zero m e he]
  exact hAe

theorem inverse {m : ℕ} {S : SmoothSeparation X Y (Space (m+3))}
    {B : X → Space (m+3) → ℂ} {C : Y → Space (m+3) → ℂ}
    (A : SeparationSupport S B C) (j : ℕ) :
    ∃ U : SeparationSupport (S.inverse m j) B C,
      ∀ e : Sphere (m+3),
        ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 →
        A.At e e e → U.At e e e := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [SmoothSeparation.inverse]
      exact ⟨A.mulLeft _ _,fun _ _ h => h⟩
    | succ j =>
      have hh (k : Fin (j+1)) := ih (j-k) (by have hk := k.isLt; omega)
      choose U hU using hh
      have hj (k : Fin (j+1)) := (U k).stationaryJet (j := (k:ℕ)+1)
      choose T hT using hj
      rw [SmoothSeparation.inverse]
      refine ⟨(sum T).mulLeft _ _,?_⟩
      intro e he hAe i
      exact hT i.1 e he (hU i.1 e he hAe) i.2

end SeparationSupport

theorem localInverseAmplitude_product_factors (m j : ℕ)
    (B : X → Space (m+3) → ℂ) (C : Y → Space (m+3) → ℂ)
    (hB : ∀ x, ContDiff ℝ ∞ (B x)) (hC : ∀ y, ContDiff ℝ ∞ (C y)) :
    ∃ S : SmoothSeparation X Y (Space (m+3)),
      S.HasOrder B C (2*j) ∧
      (∀ x y e, localInverseAmplitude m (fun w => B x w*C y w) j e = S.value x y e) ∧
      ∀ e : Sphere (m+3),
        ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 →
        ∀ i : S.index,
          (∀ x, S.left i x e ≠ 0 → (e : Space (m+3)) ∈ tsupport (B x)) ∧
          (∀ y, S.right i y e ≠ 0 → (e : Space (m+3)) ∈ tsupport (C y)) := by
  let P := SmoothSeparation.product B C hB hC
  obtain ⟨U,hU⟩ := (SeparationSupport.product B C hB hC).inverse (m := m) j
  refine ⟨P.inverse m j,?_,?_,?_⟩
  · simpa only [Nat.zero_add] using (SmoothSeparation.product_hasOrder B C hB hC).inverse j
  · intro x y e
    rw [SmoothSeparation.inverse_value]
    have hp : P.value x y = fun w => B x w*C y w := by
      funext w
      exact SmoothSeparation.product_value B C hB hC x y w
    rw [hp]
  · intro e he i
    have ha : U.At e e e := hU e he (fun _ => ⟨rfl,rfl⟩)
    exact ⟨fun x hx => U.left_mem_of_ne_zero ha i x hx,
      fun y hy => U.right_mem_of_ne_zero ha i y hy⟩

end Falconer

end OAI
