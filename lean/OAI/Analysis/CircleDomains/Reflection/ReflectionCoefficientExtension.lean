import OAI.Analysis.CircleDomains.Reflection.ReflectionCoefficientWords

namespace OAI

/-! A bounded measurable coefficient on the base exterior extends over all
reflected tiles. The extension is zero on the residual set and satisfies
every generating reflection identity. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [Countable I] [DecidableEq I]

lemma exists_reflection_coefficient_extension
    (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i)) (K U : I → Set X)
    (hUK : ∀i,U i⊆K i) (hd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hr : ∀i,R i '' (K i)ᶜ⊆U i)
    (htm : ∀w : List I,MeasurableSet (reflectionTile R K w))
    (V : I → X → ℂ → ℂ)
    (hVinv : ∀i x a,V i x (V i (R i x) a)=a)
    (hVzero : ∀i x,V i x 0=0) (hVnorm : ∀i x a,‖V i x a‖=‖a‖)
    (hVm : ∀i,Measurable (fun p : X × ℂ => V i p.1 p.2))
    (f : X → ℂ) (hf : Measurable f) {k : ℝ} (hk : 0≤k) (hb : ∀x,‖f x‖≤k) :
    ∃ E : X → ℂ,Measurable E ∧ (∀x,‖E x‖≤k) ∧
      EqOn E f (⋃i,K i)ᶜ ∧
      (∀x,x∉⋃w : {w : List I // w.IsChain (·≠·)},reflectionTile R K w.val → E x=0) ∧
      ∀i x,E x=V i x (E (R i x)) := by
  classical
  let W := {w : List I // w.IsChain (·≠·)}
  let B := ⋃w : W,reflectionTile R K w.val
  let T : Option W → Set X := fun a => match a with
    | none => Bᶜ
    | some w => reflectionTile R K w.val
  let g : Option W → X → ℂ := fun a => match a with
    | none => fun _ => 0
    | some w => reflectionCoefficientWord R V w.val f
  have hTm : ∀a,MeasurableSet (T a) := by
    intro a
    cases a with
    | none => exact (MeasurableSet.iUnion (fun w : W => htm w.val)).compl
    | some w => exact htm w.val
  have hgm : ∀a,Measurable (g a) := by
    intro a
    cases a with
    | none => exact measurable_const
    | some w => exact reflectionCoefficientWord_measurable R V hVm f hf w.val
  have hTd : Pairwise (fun a b => Disjoint (T a) (T b)) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some w =>
        apply Set.disjoint_left.mpr
        intro x hx hxw
        exact hx (mem_iUnion.mpr ⟨w,hxw⟩)
    | some w =>
      cases b with
      | none =>
        apply Set.disjoint_left.mpr
        intro x hxw hx
        exact hx (mem_iUnion.mpr ⟨w,hxw⟩)
      | some v =>
        exact reflectionTiles_pairwise_disjoint R K U hUK hd hr
          (fun he => hab (congrArg some he))
  obtain ⟨E,hEm,hE⟩ := exists_measurable_piecewise T hTm g hgm (by
    intro a b hab x hx
    exact (Set.disjoint_left.mp (hTd hab) hx.1 hx.2).elim)
  have hEoff (x : X) (hx : x∉B) : E x=0 := hE none hx
  have hEtile (w : W) {x : X} (hx : x∈reflectionTile R K w.val) :
      E x=reflectionCoefficientWord R V w.val f x := hE (some w) hx
  refine ⟨E,hEm,?_,?_,hEoff,?_⟩
  · intro x
    by_cases hx : x∈B
    · obtain ⟨w,hw⟩ := mem_iUnion.mp hx
      rw [hEtile w hw]
      exact reflectionCoefficientWord_bound R V hVnorm f hb w.val x
    · rw [hEoff x hx,norm_zero]
      exact hk
  · intro x hx
    let w : W := ⟨[],by simp⟩
    exact hEtile w (by simpa only [w,reflectionTile_nil] using hx)
  · intro i x
    by_cases hx : x∈B
    · obtain ⟨w,hw⟩ := mem_iUnion.mp hx
      let v : W := ⟨reflectionReduceStep i w.val,reflectionReduceStep_isChain i w.val w.property⟩
      have hv : R i x∈reflectionTile R K v.val := by
        rw [show v.val=reflectionReduceStep i w.val from rfl,reflectionTile_reduceStep R hR]
        exact mem_image_of_mem (R i) hw
      rw [hEtile w hw,hEtile v hv]
      change reflectionCoefficientWord R V w.val f x=
        V i x (reflectionCoefficientWord R V (reflectionReduceStep i w.val) f (R i x))
      rw [reflectionCoefficientWord_reduceStep R hR V hVinv,hR i]
      exact (hVinv i x _).symm
    · have hy : R i x∉B := by
        intro hy
        have hm := mem_image_of_mem (R i) hy
        rw [reflection_tiles_union_invariant R hR K i] at hm
        rw [hR i] at hm
        exact hx hm
      rw [hEoff x hx,hEoff (R i x) hy,hVzero]

end CircleDomainRigidity

end

end OAI
